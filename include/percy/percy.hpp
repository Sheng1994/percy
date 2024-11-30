#pragma once

#include <chrono>
#include <memory>
#include <thread>
#include <mutex>
#include "spec.hpp"
#include "fence.hpp"
#include "chain.hpp"
#include "chain_3in.hpp"
#include "mig.hpp"
#include "dag_generation.hpp"
#include "tt_utils.hpp"
#include "concurrentqueue.h"
#include "partial_dag.hpp"
#include "solvers.hpp"
#include "encoders.hpp"
#include "cnf.hpp"
#include <limits>

/*******************************************************************************
	This module defines the interface to synthesize Boolean chains from
	specifications. The inspiration for this module is taken from Mathias
	Soeken's earlier exact synthesis algorithm, which has been integrated in
	the ABC synthesis package. That implementation is itself based on earlier
	work by Éen[1] and Knuth[2].

	[1] Niklas Éen, "Practical SAT – a tutorial on applied satisfiability
	solving," 2007, slides of invited talk at FMCAD.
	[2] Donald Ervin Knuth, "The Art of Computer Programming, Volume 4,
	Fascicle 6: Satisfiability," 2015
*******************************************************************************/
namespace percy
{
	using std::chrono::high_resolution_clock;
	using std::chrono::duration;
	using std::chrono::time_point;

	bool check_dag_equal(partial_dag g0, partial_dag g1);
	inline synth_result
		pd_synthesize_parallel_rec(
			std::vector<spec>& spec_all,
			std::vector<chain>& c_all,
			std::vector<partial_dag>& dags,
			int nr_dag);
	inline synth_result pd_ser_synthesize_parallel(
		spec& spec,
		chain& c,
		std::vector<partial_dag> dags,
		int nr_dag);

	const int PD_SIZE_CONST = 1000; // Some "impossibly large" number

	static inline bool is_trivial(const kitty::dynamic_truth_table& tt)
	{
		kitty::dynamic_truth_table tt_check(tt.num_vars());

		if (tt == tt_check || tt == ~tt_check) {
			return true;
		}

		for (auto i = 0; i < tt.num_vars(); i++) {
			kitty::create_nth_var(tt_check, i);
			if (tt == tt_check || tt == ~tt_check) {
				return true;
			}
		}

		return false;
	}

	inline synth_result
		std_synthesize(
			spec& spec,
			chain& chain,
			solver_wrapper& solver,
			std_encoder& encoder,
			synth_stats* stats = NULL)
	{
		assert(spec.get_nr_in() >= spec.fanin);
		spec.preprocess();

		if (stats) {
			stats->synth_time = 0;
			stats->sat_time = 0;
			stats->unsat_time = 0;
			stats->nr_vars = 0;
			stats->nr_clauses = 0;
		}

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			chain.reset(spec.get_nr_in(), spec.get_nr_out(), 0, spec.fanin);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				chain.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		spec.nr_steps = spec.initial_steps;
		//spec.nr_steps = 7;
		while (true) {
			solver.restart();
			if (!encoder.encode(spec)) {
				spec.nr_steps++;
				continue;
			}
			if (stats) {
				stats->nr_vars = solver.nr_vars();
				stats->nr_clauses = solver.nr_clauses();
			}

			auto begin = std::chrono::steady_clock::now();
			const auto status = solver.solve(spec.conflict_limit);
			auto end = std::chrono::steady_clock::now();
			auto elapsed_time =
				std::chrono::duration_cast<std::chrono::microseconds>(
					end - begin
					).count();

			if (stats) {
				stats->synth_time += elapsed_time;
			}

			if (status == success) {
				encoder.extract_chain(spec, chain);
				if (spec.verbosity > 2) {
					//    encoder.print_solver_state(spec);
				}
				if (stats) {
					stats->sat_time += elapsed_time;
				}
				return success;
			}
			else if (status == failure) {
				if (stats) {
					stats->unsat_time += elapsed_time;
				}
				spec.nr_steps++;
			}
			else {
				return timeout;
			}
		}
	}

	inline synth_result
		std_cegar_synthesize(
			spec& spec,
			chain& chain,
			solver_wrapper& solver,
			std_cegar_encoder& encoder,
			synth_stats* stats = NULL)
	{
		assert(spec.get_nr_in() >= spec.fanin);
		spec.preprocess();

		if (stats) {
			stats->synth_time = 0;
			stats->sat_time = 0;
			stats->unsat_time = 0;
		}

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			chain.reset(spec.get_nr_in(), spec.get_nr_out(), 0, spec.fanin);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				chain.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		encoder.reset_sim_tts(spec.nr_in);
		spec.nr_steps = spec.initial_steps;
		while (true) {
			solver.restart();
			if (!encoder.cegar_encode(spec)) {
				spec.nr_steps++;
				continue;
			}
			auto iMint = 1;
			for (int i = 0; iMint != -1; i++) {
				if (!encoder.create_tt_clauses(spec, iMint - 1)) {
					break;
				}
				auto begin = std::chrono::steady_clock::now();
				auto stat = solver.solve(spec.conflict_limit);
				auto end = std::chrono::steady_clock::now();
				auto elapsed_time =
					std::chrono::duration_cast<std::chrono::microseconds>(
						end - begin
						).count();
				if (stats) {
					stats->synth_time += elapsed_time;
				}
				if (stat == failure) {
					if (stats) {
						stats->unsat_time += elapsed_time;
					}
					break;
				}
				else {
					if (stats) {
						stats->sat_time += elapsed_time;
					}
				}
				iMint = encoder.simulate(spec);
			}
			if (iMint == -1) {
				encoder.cegar_extract_chain(spec, chain);
				break;
			}
			spec.nr_steps++;
		}

		return synth_result::success;
	}

	inline std::unique_ptr<solver_wrapper>
		get_solver(SolverType type = SLV_BSAT2)
	{
		solver_wrapper* solver = nullptr;
		std::unique_ptr<solver_wrapper> res;

		switch (type) {
		case SLV_BSAT2:
			solver = new bsat_wrapper;
			break;
#ifdef USE_CMS
		case SLV_CMSAT:
			solver = new cmsat_wrapper;
			break;
#endif
#if defined(USE_GLUCOSE) || defined(USE_SYRUP)
		case SLV_GLUCOSE:
			solver = new glucose_wrapper;
			break;
#endif
#ifdef USE_SATOKO
		case SLV_SATOKO:
			solver = new satoko_wrapper;
			break;
#endif
		default:
			fprintf(stderr, "Error: solver type %d not found", type);
			exit(1);
		}

		res.reset(solver);
		return res;
	}

	inline std::unique_ptr<encoder>
		get_encoder(solver_wrapper& solver, EncoderType enc_type = ENC_SSV)
	{
		encoder* enc = nullptr;
		std::unique_ptr<encoder> res;

		switch (enc_type) {
		case ENC_SSV:
			enc = new ssv_encoder(solver);
			break;
		case ENC_MSV:
			enc = new msv_encoder(solver);
			break;
		case ENC_DITT:
			enc = new ditt_encoder(solver);
			break;
		case ENC_FENCE:
			enc = new ssv_fence_encoder(solver);
			break;
		case ENC_DAG:
			enc = new ssv_dag_encoder<2>();
			break;
		default:
			fprintf(stderr, "Error: encoder type %d not found\n", enc_type);
			exit(1);
		}

		res.reset(enc);
		return res;
	}

	inline synth_result
		fence_synthesize(spec& spec, chain& chain, solver_wrapper& solver, fence_encoder& encoder)
	{
		assert(spec.get_nr_in() >= spec.fanin);
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			chain.reset(spec.get_nr_in(), spec.get_nr_out(), 0, spec.fanin);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				chain.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		// As the topological synthesizer decomposes the synthesis
		// problem, to fairly count the total number of conflicts we
		// should keep track of all conflicts in existence checks.
		fence f;
		po_filter<unbounded_generator> g(
			unbounded_generator(spec.initial_steps),
			spec.get_nr_out(), spec.fanin);
		int old_nnodes = 1;
		auto total_conflicts = 0;
		while (true) {
			g.next_fence(f);
			spec.nr_steps = f.nr_nodes();

			if (spec.nr_steps > old_nnodes) {
				// Reset conflict count, since this is where other
				// synthesizers reset it.
				total_conflicts = 0;
				old_nnodes = spec.nr_steps;
			}

			solver.restart();
			if (!encoder.encode(spec, f)) {
				continue;
			}

			if (spec.verbosity) {
				printf("  next fence:\n");
				print_fence(f);
				printf("\n");
				printf("nr_nodes=%d, nr_levels=%d\n", f.nr_nodes(),
					f.nr_levels());
				for (int i = 0; i < f.nr_levels(); i++) {
					printf("f[%d] = %d\n", i, f[i]);
				}
			}
			auto status = solver.solve(spec.conflict_limit);
			if (status == success) {
				encoder.extract_chain(spec, chain);
				return success;
			}
			else if (status == failure) {
				total_conflicts += solver.nr_conflicts();
				if (spec.conflict_limit &&
					total_conflicts > spec.conflict_limit) {
					return timeout;
				}
				continue;
			}
			else {
				return timeout;
			}
		}
	}

	inline synth_result
		fence_synthesize_rec(
			std::vector<spec>& spec_all,
			std::vector<chain>& c)
	{
		for (int i = 1; i < spec_all.size(); i++) { // verify if the input number equals
			assert(spec_all[i - 1].get_nr_in() >= spec_all[i].fanin);
		}
		for (int i = 0; i < spec_all.size(); i++) { // preprocess
			spec_all[i].preprocess();
		}

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		for (int i = 0; i < spec_all.size(); i++) {
			if (spec_all[i].nr_triv == spec_all[i].get_nr_out()) {
				c[0].reset(spec_all[i].get_nr_in(), spec_all[i].get_nr_out(), 0, spec_all[i].fanin);
				for (int h = 0; h < spec_all[i].get_nr_out(); h++) {
					c[0].set_output(h, (spec_all[i].triv_func(h) << 1) +
						((spec_all[i].out_inv >> h) & 1));
				}
				return success;
			}
		}
		bsat_wrapper solver;
		ssv_fence2_encoder encoder(solver);
		//spec_all[0].conflict_limit = 10;
		// As the topological synthesizer decomposes the synthesis
		// problem, to fairly count the total number of conflicts we
		// should keep track of all conflicts in existence checks.
		fence f;
		po_filter<unbounded_generator> g(
			unbounded_generator(spec_all[0].initial_steps),
			spec_all[0].get_nr_out(), spec_all[0].fanin);
		int old_nnodes = 1;
		auto total_conflicts = 0;
		while (true) {
			g.next_fence(f);
			spec_all[0].nr_steps = f.nr_nodes();
			spec_all[1].nr_steps = spec_all[0].nr_steps;

			if (spec_all[0].nr_steps > old_nnodes) {
				// Reset conflict count, since this is where other
				// synthesizers reset it.
				total_conflicts = 0;
				old_nnodes = spec_all[0].nr_steps;
			}
			bool found = false;
			synth_result status;
			solver.restart();

			if (spec_all[0].verbosity) {
				printf("  next fence:\n");
				print_fence(f);
				printf("\n");
				printf("nr_nodes=%d, nr_levels=%d\n", f.nr_nodes(),
					f.nr_levels());
				for (int i = 0; i < f.nr_levels(); i++) {
					printf("f[%d] = %d\n", i, f[i]);
				}
			}
			if (!encoder.encode_nc(spec_all, f)) { // encode fence and truth table to clauses
				continue;
			}
			do {
				status = solver.solve(10);
				if (status == success) {
					if (!(found)) {
						for (int ispec = 0; ispec < spec_all.size(); ispec++) {
							encoder.extract_chain_nc(spec_all[ispec], c[ispec], ispec); // clauses to boolean chain
						}
						found = true;
						break;
					}
				}
			} while (status == timeout);
			if (found) {
				break;
			}
			if (spec_all[0].nr_steps > 9) {
				return failure;
			}
			/*auto status = solver.solve(spec_all[0].conflict_limit);
			if (status == success) {
				for (int ispec = 0; ispec < spec_all.size(); ispec++) {
					encoder.extract_chain_nc(spec_all[ispec], c[ispec], ispec); // clauses to boolean chain
				}
				return success;
			}
			else if (status == failure) {
				total_conflicts += solver.nr_conflicts();
				if (spec_all[0].conflict_limit &&
					total_conflicts > spec_all[0].conflict_limit) {
					return timeout;
				}
				continue;
			}
			else {
				return timeout;
			}*/
		}
		return success;
	}

	/// Synthesizes a chain using a set of serialized partial DAGs.
	inline synth_result pd_ser_synthesize_sorted_rec(
		std::vector<spec>& spec_all,
		std::vector<chain>& c,
		solver_wrapper& solver,
		partial_dag_encoder& encoder,
		int minpis,
		bool fpi_new,
		std::string file_prefix = "",
		int max_time = std::numeric_limits<int>::max()) // Timeout in seconds
	{
		for (int i = 1; i < spec_all.size(); i++) { // verify if the input number equals
			assert(spec_all[i - 1].get_nr_in() >= spec_all[i].fanin);
		}
		for (int i = 0; i < spec_all.size(); i++) { // preprocess
			spec_all[i].preprocess();
		}

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		for (int i = 0; i < spec_all.size(); i++) {
			if (spec_all[i].nr_triv == spec_all[i].get_nr_out()) {
				c[0].reset(spec_all[i].get_nr_in(), spec_all[i].get_nr_out(), 0, spec_all[i].fanin);
				for (int h = 0; h < spec_all[i].get_nr_out(); h++) {
					c[0].set_output(h, (spec_all[i].triv_func(h) << 1) +
						((spec_all[i].out_inv >> h) & 1));
				}
				return success;
			}
		}
		spec_all[0].nr_steps = spec_all[0].initial_steps;
		spec_all[1].nr_steps = spec_all[0].nr_steps;

		std::vector<std::string> dags_sorted;
		std::vector<int> vser_pis, vnr_dags, vbad_dag, vdag_tried;
		partial_dag g;
		if (fpi_new == false){
			if (spec_all[0].nr_in == 6) {
				dags_sorted.insert(dags_sorted.end(), { "pd5_6.bin","pd6_6.bin","pd6_7.bin",
					"pd7_6.bin","pd7_7.bin","pd7_8.bin","pd8_6.bin","pd8_7.bin","pd8_8.bin",
					"pd8_9.bin","pd9_6.bin","pd9_7.bin","pd9_8.bin","pd9_9.bin","pd9_10.bin" });

				vser_pis.insert(vser_pis.end(), { 6,6,7,6,7,8,6,7,8,9,6,7,8,9,10 });
				vnr_dags.insert(vnr_dags.end(), { 13,116,43,964,581,143,8659,6671,2811,570,86855,78187,43411,15181,2303 });
				std::vector<int> vbad_dag_(15, 0), vdag_tried_(15, 0);
				vbad_dag = vbad_dag_;
				vdag_tried = vdag_tried_;
			}
			else if (spec_all[0].nr_in == 5)
			{
				dags_sorted.insert(dags_sorted.end(), { "pd4_5.bin","pd5_5.bin","pd5_6.bin",
					"pd6_5.bin","pd6_6.bin","pd6_7.bin","pd7_5.bin","pd7_6.bin","pd7_7.bin","pd7_8.bin",
					"pd8_5.bin","pd8_6.bin","pd8_7.bin","pd8_8.bin","pd8_9.bin",
					"pd9_5.bin","pd9_6.bin","pd9_7.bin","pd9_8.bin","pd9_9.bin","pd9_9.bin","pd9_10.bin" });

				vser_pis.insert(vser_pis.end(), { 5,5,6,5,6,7,5,6,7,8,5,6,7,8,9,5,6,7,8,9,10 });
				vnr_dags.insert(vnr_dags.end(), { 26,13,146,116,43,962,964,581,143,7463,8659,6671,2811,570,67443,86855,78187,43411,15181,2303 });
				std::vector<int> vbad_dag_(21, 0), vdag_tried_(21, 0);
				vbad_dag = vbad_dag_;
				vdag_tried = vdag_tried_;
			}
		}
		else {
			std::vector<int> vmaxpi = { 5,9,15,23,38,61 };
			if (spec_all[0].nr_steps == 5) {
				for (int i = 4; i <= 9; i++) {
					//for (int j = i; j < vmaxpi[i - 4]; j++) {
					for (int j = vmaxpi[i - 4]-1; j >= i; j--) {
						std::string setname = "pd" + std::to_string(i) + '_' + std::to_string(j + 1) + ".bin";
						dags_sorted.insert(dags_sorted.end(), setname);
					}
				}
			}
		}

		auto begin = std::chrono::steady_clock::now();
		for (int pd_id = 0; pd_id < dags_sorted.size(); pd_id++) {
			//std::size_t pos = dags_sorted[pd_id].find("_");
			int ser_pis = stoi(dags_sorted[pd_id].substr(4));
			if (ser_pis < minpis) {  // filter of pi
				continue;
			}

			g.reset(2, int(dags_sorted[pd_id][2]) - int('0'));
			spec_all[0].nr_steps = spec_all[1].nr_steps = int(dags_sorted[pd_id][2]) - int('0');
			const auto filename = file_prefix + dags_sorted[pd_id];
			auto fhandle = fopen(filename.c_str(), "rb");
			if (fhandle == NULL) {
				fprintf(stderr, "Error: unable to open file %s\n", filename.c_str());
				break;
			}

			int buf;
			while (fread(&buf, sizeof(int), 1, fhandle) != 0) {
				for (int i = 0; i < spec_all[0].nr_steps; i++) {
					auto read = fread(&buf, sizeof(int), 1, fhandle);
					assert(read > 0);
					auto fanin1 = buf;
					read = fread(&buf, sizeof(int), 1, fhandle);
					assert(read > 0);
					auto fanin2 = buf;
					g.set_vertex(i, fanin1, fanin2);
				}
				/*vdag_tried[pd_id]++;
				if (!g.check_dag(spec_all[0].nr_in))
				{
					vbad_dag[pd_id]++;
					continue;
				}*/

				solver.restart();
				if (!encoder.encode_nc(spec_all, g)) { // encode fence and truth table to clauses
					continue;
				}
				const auto status = solver.solve(0);
				auto end = std::chrono::steady_clock::now();
				auto elapsed_time =
					std::chrono::duration_cast<std::chrono::seconds>(
						end - begin
						).count();
				if (elapsed_time > max_time) {
					return timeout;
				}
				if (status == success) {
					for (int ispec = 0; ispec < spec_all.size(); ispec++) {
						encoder.extract_chain_nc(spec_all[ispec], g, c[ispec], ispec); // clauses to boolean chain
					}
					fclose(fhandle);
					return success;
				}
			}
			fclose(fhandle);
		}
		return failure;
	}

	/// Synthesizes a multi-output chain using a given partial DAGs.
	inline synth_result pd_synthesize_rec(
		std::vector<spec>& spec_all,
		std::vector<chain>& c,
		solver_wrapper& solver,
		partial_dag_encoder& encoder,
		partial_dag g,
		int max_time = std::numeric_limits<int>::max()) // Timeout in seconds
	{
		for (int i = 1; i < spec_all.size(); i++) { // verify if the input number equals
			assert(spec_all[i - 1].get_nr_in() >= spec_all[i].fanin);
		}
		for (int i = 0; i < spec_all.size(); i++) { // preprocess
			spec_all[i].preprocess();
		}

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		for (int i = 0; i < spec_all.size(); i++) {
			if (spec_all[i].nr_triv == spec_all[i].get_nr_out()) {
				c[0].reset(spec_all[i].get_nr_in(), spec_all[i].get_nr_out(), 0, spec_all[i].fanin);
				for (int h = 0; h < spec_all[i].get_nr_out(); h++) {
					c[0].set_output(h, (spec_all[i].triv_func(h) << 1) +
						((spec_all[i].out_inv >> h) & 1));
				}
				return success;
			}
		}
		for (int i = 0; i < spec_all.size(); i++) {
			spec_all[i].nr_steps = spec_all[0].initial_steps;

		}
		auto begin = std::chrono::steady_clock::now();
		solver.restart();
		if (!encoder.encode_nc(spec_all, g)) { // encode partial dag and truth table to clauses
			return failure;
		}
		const auto status = solver.solve(0);
		auto end = std::chrono::steady_clock::now();
		auto elapsed_time =
			std::chrono::duration_cast<std::chrono::seconds>(
				end - begin
				).count();
		if (elapsed_time > max_time) {
			return timeout;
		}
		if (status == success) {
			for (int ispec = 0; ispec < spec_all.size(); ispec++) {
				encoder.extract_chain_nc(spec_all[ispec], g, c[ispec], ispec); // clauses to boolean chain
			}
			return success;
		}
	}


	inline bool check_dag_equal(partial_dag g0, partial_dag g1) {
		if (g0.nr_vertices() != g1.nr_vertices()) {
			return failure;
		}
		for (int i = 0; i < g0.nr_vertices(); i++) {
			if ((g0.get_vertex(i)[0] != g1.get_vertex(i)[0]) || (g0.get_vertex(i)[1] != g1.get_vertex(i)[1]))
			{
				return failure;
			}
		}
		return success;
	}

	/// Synthesizes a chain using a set of serialized partial DAGs.
	inline synth_result pd_ser_synthesize_sorted_parallel_rec(
		std::vector<spec>& spec_all,
		std::vector<chain>& c_all,
		solver_wrapper& solver,
		partial_dag_encoder& encoder,
		int minpis,
		std::string file_prefix = "",
		int max_time = std::numeric_limits<int>::max()) // Timeout in seconds
	{
		spec_all[0].initial_steps = 5;
		for (int i = 1; i < spec_all.size(); i++) { // verify if the input number equals
			assert(spec_all[i - 1].get_nr_in() >= spec_all[i].fanin);
		}
		for (int i = 0; i < spec_all.size(); i++) { // preprocess
			spec_all[i].preprocess();
		}

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		for (int i = 0; i < spec_all.size(); i++) {
			if (spec_all[i].nr_triv == spec_all[i].get_nr_out()) {
				c_all[0].reset(spec_all[i].get_nr_in(), spec_all[i].get_nr_out(), 0, spec_all[i].fanin);
				for (int h = 0; h < spec_all[i].get_nr_out(); h++) {
					c_all[0].set_output(h, (spec_all[i].triv_func(h) << 1) +
						((spec_all[i].out_inv >> h) & 1));
				}
				return success;
			}
		}

		std::vector<std::string> dags_sorted;
		dags_sorted.insert(dags_sorted.end(), { "pd5_6.bin","pd6_6.bin","pd6_7.bin",
			"pd7_6.bin","pd7_7.bin","pd7_8.bin","pd8_6.bin","pd8_7.bin","pd8_8.bin",
			"pd8_9.bin","pd9_6.bin","pd9_7.bin","pd9_8.bin","pd9_9.bin","pd9_10.bin" });
		std::vector<int> vser_pis, vnr_dags, vbad_dag, vdag_tried;
		vser_pis.insert(vser_pis.end(), { 6,6,7,6,7,8,6,7,8,9,6,7,8,9,10 });
		vnr_dags.insert(vnr_dags.end(), { 13,116,43,964,581,143,8659,6671,2811,570,86855,78187,43411,15181,2303 });
		vdag_tried.insert(vdag_tried.end(), { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 });
		vbad_dag.insert(vbad_dag.end(), { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 });
		partial_dag g;
		spec_all[0].nr_steps = spec_all[0].initial_steps; // initial_steps = 5
		spec_all[1].nr_steps = spec_all[0].nr_steps;

		auto begin = std::chrono::steady_clock::now();
		std:vector<partial_dag> dags;
		for (int pd_id = 0; pd_id < dags_sorted.size(); pd_id++) {
			if (vser_pis[pd_id] < minpis) {  // filter of pi
				continue;
			}
			dags.clear();
			g.reset(2, int(dags_sorted[pd_id][2]) - int('0'));
			spec_all[0].nr_steps = spec_all[1].nr_steps = int(dags_sorted[pd_id][2]) - int('0');
			const auto filename = file_prefix + dags_sorted[pd_id];
			auto fhandle = fopen(filename.c_str(), "rb");
			if (fhandle == NULL) {
				fprintf(stderr, "Error: unable to open file %s\n", filename.c_str());
				break;
			}

			int buf;
			while (fread(&buf, sizeof(int), 1, fhandle) != 0) {
				for (int i = 0; i < spec_all[0].nr_steps; i++) {
					auto read = fread(&buf, sizeof(int), 1, fhandle);
					assert(read > 0);
					auto fanin1 = buf;
					read = fread(&buf, sizeof(int), 1, fhandle);
					assert(read > 0);
					auto fanin2 = buf;
					g.set_vertex(i, fanin1, fanin2);
				}
				vdag_tried[pd_id]++;
				if (!g.check_dag(spec_all[0].nr_in))
				{
					vbad_dag[pd_id]++;
					continue;
				}
				dags.push_back(g);
			}

			fclose(fhandle);
			synth_result res = pd_synthesize_parallel_rec(spec_all, c_all, dags, vnr_dags[pd_id]);
			if (res == success) {
				return success;
			}
		}
		return failure;
	}


	inline synth_result
		pd_synthesize_parallel_rec(
			std::vector<spec>& spec_all,
			std::vector<chain>& c_all,
			std::vector<partial_dag>& dags,
			int nr_dag)
	{
		int num_threads = std::thread::hardware_concurrency();
		std::vector<std::thread> threads(num_threads);
		moodycamel::ConcurrentQueue<partial_dag> q(num_threads * 3);
		bool finished_generating = false;
		bool* pfinished = &finished_generating;
		int size_found = PD_SIZE_CONST;
		int* psize_found = &size_found;
		std::mutex found_mutex;

		for (int i = 0; i < num_threads; i++) {
			threads[i] = std::thread([&spec_all, psize_found, pfinished, &found_mutex, &c_all, &q] {
				percy::spec local_spec = spec_all[0];
				bsat_wrapper solver;
				partial_dag_encoder encoder(solver);
				partial_dag dag;
				local_spec.nr_steps = 0;

				while (*psize_found > local_spec.nr_steps) {
					if (!q.try_dequeue(dag)) {
						if (*pfinished) {
							std::this_thread::yield();
							if (!q.try_dequeue(dag)) {
								break;
							}
						}
						else {
							std::this_thread::yield();
							continue;
						}
					}
					local_spec.nr_steps = dag.nr_vertices();
					synth_result status;
					solver.restart();
					if (!encoder.encode_nc(spec_all, dag)) {
						continue;
					}
					while (true) {
						status = solver.solve(10);
						if (status == failure) {
							break;
						}
						else if (status == success) {
							std::lock_guard<std::mutex> vlock(found_mutex);
							if (*psize_found > local_spec.nr_steps) {
								for (int ispec = 0; ispec < spec_all.size(); ispec++) {
									encoder.extract_chain_nc(spec_all[ispec], dag, c_all[ispec], ispec); // clauses to boolean chain
								}
								*psize_found = local_spec.nr_steps;
							}
							break;
						}
						else if (*psize_found <= local_spec.nr_steps) {
							// Another thread found a solution that's
							// better or equal to this one.
							break;
						}

					}
				}
				});
		}
		size_t dag_idx = 0;
		while (size_found == PD_SIZE_CONST) {
			while (!q.try_enqueue(dags[dag_idx])) {
				if (size_found == PD_SIZE_CONST) {
					std::this_thread::yield();
				}
				else {
					break;
				}
			}
			if (dag_idx + 1 == nr_dag) {
				break;
			}
			dag_idx++;
		}
		finished_generating = true;
		for (auto& thread : threads) {
			thread.join();
		}
		if (size_found < 10) {
			return success;
		}
		return failure;
	}

	inline synth_result
		fence_synthesize(
			spec& spec,
			chain& chain,
			solver_wrapper& solver,
			fence_encoder& encoder,
			fence& fence)
	{
		solver.restart();
		if (!encoder.encode(spec, fence)) {
			return failure;
		}
		auto status = solver.solve(spec.conflict_limit);
		if (status == success) {
			encoder.extract_chain(spec, chain);
		}
		return status;
	}

	// try to obtain a basic recfigurable synthesizer
	inline synth_result
		fence_synthesize_rec(
			std::vector<spec>& spec_all,
			std::vector<chain>& c,
			fence local_fence)
	{
		bsat_wrapper solver;
		ssv_fence2_encoder encoder(solver);

		solver.restart();
		if (!encoder.encode_nc(spec_all, local_fence)) {
			return failure;
		}
		auto status = solver.solve(10);
		if (status == success) {
			for (int ispec = 0; ispec < spec_all.size(); ispec++) {
				encoder.extract_chain_nc(spec_all[ispec], c[ispec], ispec);
			}
		}
		return status;
	}


	inline synth_result
		fence_cegar_synthesize(
			spec& spec,
			chain& chain,
			solver_wrapper& solver,
			fence_encoder& encoder,
			fence& fence)
	{
		solver.restart();
		if (!encoder.cegar_encode(spec, fence)) {
			return failure;
		}

		while (true) {
			auto status = solver.solve(spec.conflict_limit);
			if (status == success) {
				auto sim_tt = encoder.simulate(spec);
				if (spec.out_inv) {
					sim_tt = ~sim_tt;
				}
				auto xor_tt = sim_tt ^ (spec[0]);
				auto first_one = kitty::find_first_one_bit(xor_tt);
				if (first_one == -1) {
					encoder.extract_chain(spec, chain);
					return success;
				}
				// Add additional constraint.
				if (spec.verbosity) {
					printf("  CEGAR difference at tt index %ld\n",
						first_one);
				}
				if (!encoder.create_tt_clauses(spec, first_one - 1)) {
					return failure;
				}
			}
			else {
				return status;
			}
		}
	}

	inline synth_result
		fence_cegar_synthesize(spec& spec, chain& chain, solver_wrapper& solver, fence_encoder& encoder)
	{
		assert(spec.get_nr_in() >= spec.fanin);

		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			chain.reset(spec.get_nr_in(), spec.get_nr_out(), 0, spec.fanin);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				chain.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		encoder.reset_sim_tts(spec.nr_in);

		fence f;
		po_filter<unbounded_generator> g(
			unbounded_generator(spec.initial_steps),
			spec.get_nr_out(), spec.fanin);
		while (true) {
			g.next_fence(f);
			spec.nr_steps = f.nr_nodes();

			if (spec.verbosity) {
				printf("  next fence:\n");
				print_fence(f);
				printf("\n");
				printf("nr_nodes=%d, nr_levels=%d\n", f.nr_nodes(),
					f.nr_levels());
				for (int i = 0; i < f.nr_levels(); i++) {
					printf("f[%d] = %d\n", i, f[i]);
				}
			}

			solver.restart();
			if (!encoder.cegar_encode(spec, f)) {
				continue;
			}
			while (true) {
				auto status = solver.solve(spec.conflict_limit);
				if (status == success) {
					auto sim_tt = encoder.simulate(spec);
					if (spec.out_inv) {
						sim_tt = ~sim_tt;
					}
					auto xor_tt = sim_tt ^ (spec[0]); // find the difference between current tt and target tt
					if (spec.has_dc_mask(0)) {
						xor_tt &= ~spec.get_dc_mask(0);
					}
					auto first_one = kitty::find_first_one_bit(xor_tt);
					if (first_one == -1) {
						encoder.extract_chain(spec, chain);
						return success;
					}
					if (!encoder.create_tt_clauses(spec, first_one - 1)) {
						break; // if the clause to be added is empty
					}
				}
				else if (status == failure) {
					break;
				}
				else {
					return timeout;
				}
			}
		}
	}

	///< TODO: implement
	/*
	inline synth_result
	dag_synthesize(spec& spec, chain& chain, solver_wrapper& solver, dag_encoder<2>& encoder)
	{
		return failure;
	}
	*/

	inline synth_result
		synthesize(
			spec& spec,
			chain& chain,
			solver_wrapper& solver,
			encoder& encoder,
			SynthMethod synth_method = SYNTH_STD,
			synth_stats* stats = NULL)
	{
		switch (synth_method) {
		case SYNTH_STD:
			return std_synthesize(spec, chain, solver, static_cast<std_encoder&>(encoder), stats);
		case SYNTH_STD_CEGAR:
			return std_cegar_synthesize(spec, chain, solver, static_cast<std_cegar_encoder&>(encoder), stats);
		case SYNTH_FENCE:
			return fence_synthesize(spec, chain, solver, static_cast<fence_encoder&>(encoder));
		case SYNTH_FENCE_CEGAR:
			return fence_cegar_synthesize(spec, chain, solver, static_cast<fence_encoder&>(encoder));
			//   case SYNTH_DAG:
			 //      return dag_synthesize(spec, chain, solver, static_cast<dag_encoder<2>&>(encoder));
		default:
			fprintf(stderr, "Error: synthesis method %d not supported\n", synth_method);
			exit(1);
		}
	}

	inline synth_result
		pd_synthesize(
			spec& spec,
			chain& chain,
			const partial_dag& dag,
			solver_wrapper& solver,
			partial_dag_encoder& encoder)
	{
		assert(spec.get_nr_in() >= spec.fanin);
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
				// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			chain.reset(spec.get_nr_in(), spec.get_nr_out(), 0, spec.fanin);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				chain.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		spec.nr_steps = dag.nr_vertices();
		solver.restart();
		if (!encoder.encode(spec, dag)) {
			return failure;
		}

		synth_result status;
		status = solver.solve(0);

		if (status == success) {
			encoder.extract_chain(spec, dag, chain);
			if (spec.verbosity > 2) {
				//    encoder.print_solver_state(spec);
			}
			return success;
		}
		else if (status == failure) {
			return failure;
		}
		else {
			return percy::synth_result::timeout;
		}
	}

	// multiple outputs
	inline synth_result
		pd_synthesize_mo(
			spec& spec,
			chain& chain,
			const partial_dag& dag,
			solver_wrapper& solver,
			partial_dag_encoder& encoder)
	{
		assert(spec.get_nr_in() >= spec.fanin);
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
				// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			chain.reset(spec.get_nr_in(), spec.get_nr_out(), 0, spec.fanin);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				chain.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		spec.nr_steps = dag.nr_vertices();
		solver.restart();
		if (!encoder.encode_mo(spec, dag)) {
			return failure;
		}
		int nclauses = solver.nr_clauses();
		int nVar = solver.nr_vars();
		synth_result status;
		status = solver.solve(0);

		if (status == success) {
			encoder.extract_chain_mo(spec, dag, chain);
			if (spec.verbosity > 2) {
				encoder.print_solver_state_mo(spec, dag);
				//encoder.print_solver_state(spec, dag);
			}
			return success;
		}
		else if (status == failure) {
			return failure;
		}
		else {
			return percy::synth_result::timeout;
		}
	}

	/*inline synth_result
		pd_synthesize_pi(
			spec& spec,
			chain& chain,
			const partial_dag& dag,
			solver_wrapper& solver,
			partial_dag_encoder& encoder,
			int ifgivepi)
	{
		assert(spec.get_nr_in() >= spec.fanin);
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
				// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			chain.reset(spec.get_nr_in(), spec.get_nr_out(), 0, spec.fanin);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				chain.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		spec.nr_steps = dag.nr_vertices();
		solver.restart();
		if (!encoder.encode(spec, dag, ifgivepi)) {
			return failure;
		}

		synth_result status;
		status = solver.solve(0);

		if (status == success) {
			encoder.extract_chain(spec, dag, chain, ifgivepi);
			if (spec.verbosity > 2) {
				//    encoder.print_solver_state(spec);
			}
			return success;
		}
		else if (status == failure) {
			return failure;
		}
		else {
			return percy::synth_result::timeout;
		}
	}*/

	inline synth_result pd_cegar_synthesize(
		spec& spec,
		chain& chain,
		const partial_dag& dag,
		solver_wrapper& solver,
		partial_dag_encoder& encoder)
	{
		spec.nr_steps = dag.nr_vertices();
		solver.restart();
		if (!encoder.cegar_encode(spec, dag)) {
			return failure;
		}
		while (true) {
			auto stat = solver.solve(0);

			if (stat == success) {
				auto sim_tt = encoder.simulate(spec, dag);
				if (spec.out_inv) {
					sim_tt = ~sim_tt;
				}
				auto xor_tt = sim_tt ^ (spec[0]);
				auto first_one = kitty::find_first_one_bit(xor_tt);
				if (first_one == -1) {
					encoder.extract_chain(spec, dag, chain);
					return success;
				}
				// Add additional constraint.
				if (spec.verbosity) {
					printf("  CEGAR difference at tt index %ld\n",
						first_one);
				}
				if (!encoder.create_tt_clauses(spec, dag, first_one - 1)) {
					return failure;
				}
				else if (!encoder.fix_output_sim_vars(spec, first_one - 1)) {
					return failure;
				}
			}
			else {
				return failure;
			}
		}
	}

	inline synth_result
		pd_synthesize_enum(
			spec& spec,
			chain& chain,
			const partial_dag& dag)
	{
		partial_dag_generator gen;
		chain.reset(spec.get_nr_in(), 1, dag.nr_vertices(), 2);
		chain.set_output(0, (spec.get_nr_in() + dag.nr_vertices()) << 1);

		const auto found_sol = gen.search_sol(spec, chain, dag, 0);
		if (found_sol) {
			return success;
		}
		else {
			return failure;
		}
	}

	inline synth_result
		pd_synthesize_enum(
			spec& spec,
			chain& chain,
			const std::vector<partial_dag>& dags)
	{
		partial_dag_generator gen;
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			chain.reset(spec.get_nr_in(), spec.get_nr_out(), 0, spec.fanin);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				chain.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}
		int stat = 0;
		for (const auto& dag : dags) {
			const auto result =
				pd_synthesize_enum(spec, chain, dag);
			if (result == success) {
				stat = 1;
			}
		}
		if (stat) {
			return success;
		}
		return failure;
	}

	inline synth_result pd_synthesize(
		spec& spec,
		chain& chain,
		const std::vector<partial_dag>& dags,
		solver_wrapper& solver,
		partial_dag_encoder& encoder,
		SynthMethod synth_method = SYNTH_STD)
	{
		assert(spec.get_nr_in() >= spec.fanin);
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			chain.reset(spec.get_nr_in(), spec.get_nr_out(), 0, spec.fanin);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				chain.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		for (auto& dag : dags) {
			synth_result status;
			switch (synth_method) {
			case SYNTH_STD_CEGAR:
				status = pd_cegar_synthesize(spec, chain, dag, solver, encoder);
				break;
			default:
				status = pd_synthesize(spec, chain, dag, solver, encoder);
				break;
			}
			if (status == success) {
				return success;
			}
		}
		return failure;
	}

	inline synth_result
		pd_synthesize_parallel(
			spec& spec,
			chain& c,
			const std::vector<partial_dag>& dags,
			int num_threads = std::thread::hardware_concurrency())
	{
		assert(spec.get_nr_in() >= spec.fanin);
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			c.reset(spec.get_nr_in(), spec.get_nr_out(), 0, spec.fanin);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				c.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		std::vector<std::thread> threads(num_threads);
		moodycamel::ConcurrentQueue<partial_dag> q(num_threads * 3);

		bool finished_generating = false;
		bool* pfinished = &finished_generating;
		int size_found = PD_SIZE_CONST;
		int* psize_found = &size_found;
		std::mutex found_mutex;

		for (int i = 0; i < num_threads; i++) {
			threads[i] = std::thread([&spec, psize_found, pfinished, &found_mutex, &c, &q] {
				percy::spec local_spec = spec;
				bsat_wrapper solver;
				partial_dag_encoder encoder(solver);
				partial_dag dag;
				local_spec.nr_steps = 0;

				while (*psize_found > local_spec.nr_steps) {
					if (!q.try_dequeue(dag)) {
						if (*pfinished) {
							std::this_thread::yield();
							if (!q.try_dequeue(dag)) {
								break;
							}
						}
						else {
							std::this_thread::yield();
							continue;
						}
					}
					local_spec.nr_steps = dag.nr_vertices();
					synth_result status;
					solver.restart();
					if (!encoder.encode(local_spec, dag)) {
						continue;
					}
					while (true) {
						status = solver.solve(10);
						if (status == failure) {
							break;
						}
						else if (status == success) {
							std::lock_guard<std::mutex> vlock(found_mutex);
							if (*psize_found > local_spec.nr_steps) {
								encoder.extract_chain(local_spec, dag, c);
								*psize_found = local_spec.nr_steps;
							}
							break;
						}
						else if (*psize_found <= local_spec.nr_steps) {
							// Another thread found a solution that's
							// better or equal to this one.
							break;
						}

					}
				}
				});
		}
		size_t dag_idx = 0;
		while (size_found == PD_SIZE_CONST) {
			while (!q.try_enqueue(dags.at(dag_idx))) {
				if (size_found == PD_SIZE_CONST) {
					std::this_thread::yield();
				}
				else {
					break;
				}
			}
			dag_idx++;
		}
		finished_generating = true;
		for (auto& thread : threads) {
			thread.join();
		}

		return success;
	}

	inline synth_result
		pd_synthesize_parallel(
			spec& spec,
			chain& c,
			std::vector<partial_dag>& dags,
			int nr_dag)
	{
		int num_threads = std::thread::hardware_concurrency();

		std::vector<std::thread> threads(num_threads);
		moodycamel::ConcurrentQueue<partial_dag> q(num_threads * 3);

		bool finished_generating = false;
		bool* pfinished = &finished_generating;
		int size_found = PD_SIZE_CONST;
		int* psize_found = &size_found;
		std::mutex found_mutex;

		for (int i = 0; i < num_threads; i++) {
			threads[i] = std::thread([&spec, psize_found, pfinished, &found_mutex, &c, &q] {
				percy::spec local_spec = spec;
				bsat_wrapper solver;
				partial_dag_encoder encoder(solver);
				partial_dag dag;
				local_spec.nr_steps = 0;

				while (*psize_found > local_spec.nr_steps) {
					if (!q.try_dequeue(dag)) {
						if (*pfinished) {
							std::this_thread::yield();
							if (!q.try_dequeue(dag)) {
								break;
							}
						}
						else {
							std::this_thread::yield();
							continue;
						}
					}
					local_spec.nr_steps = dag.nr_vertices();
					synth_result status;
					solver.restart();
					if (!encoder.encode(local_spec, dag)) {
						continue;
					}
					while (true) {
						status = solver.solve(10);
						if (status == failure) {
							break;
						}
						else if (status == success) {
							std::lock_guard<std::mutex> vlock(found_mutex);
							if (*psize_found > local_spec.nr_steps) {
								encoder.extract_chain(local_spec, dag, c);
								*psize_found = local_spec.nr_steps;
							}
							break;
						}
						else if (*psize_found <= local_spec.nr_steps) {
							// Another thread found a solution that's
							// better or equal to this one.
							break;
						}

					}
				}
				});
		}
		size_t dag_idx = 0;
		while (size_found == PD_SIZE_CONST) {
			while (!q.try_enqueue(dags.at(dag_idx))) {
				if (size_found == PD_SIZE_CONST) {
					std::this_thread::yield();
				}
				else {
					break;
				}
			}
			if (dag_idx + 1 == nr_dag) {
				break;
			}
			dag_idx++;
		}
		finished_generating = true;
		for (auto& thread : threads) {
			thread.join();
		}
		return size_found == PD_SIZE_CONST ? failure : success;
	}


	/// Synthesizes a chain using a set of serialized partial DAGs.
	inline synth_result pd_ser_synthesize(
		spec& spec,
		chain& chain,
		solver_wrapper& solver,
		partial_dag_encoder& encoder,
		std::string file_prefix = "",
		int max_time = std::numeric_limits<int>::max()) // Timeout in seconds
	{
		assert(spec.get_nr_in() >= spec.fanin);
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			chain.reset(spec.get_nr_in(), spec.get_nr_out(), 0, spec.fanin);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				chain.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		partial_dag g;
		spec.nr_steps = spec.initial_steps;
		auto begin = std::chrono::steady_clock::now();
		while (true) {
			g.reset(2, spec.nr_steps);
			const auto filename = file_prefix + "pd" + std::to_string(spec.nr_steps) + ".bin";
			auto fhandle = fopen(filename.c_str(), "rb");
			if (fhandle == NULL) {
				fprintf(stderr, "Error: unable to open file %s\n", filename.c_str());
				break;
			}

			int buf;
			while (fread(&buf, sizeof(int), 1, fhandle) != 0) {
				for (int i = 0; i < spec.nr_steps; i++) {
					auto read = fread(&buf, sizeof(int), 1, fhandle);
					assert(read > 0);
					auto fanin1 = buf;
					read = fread(&buf, sizeof(int), 1, fhandle);
					assert(read > 0);
					auto fanin2 = buf;
					g.set_vertex(i, fanin1, fanin2);
				}
				solver.restart();
				if (!encoder.encode(spec, g)) {
					continue;
				}
				const auto status = solver.solve(0);
				auto end = std::chrono::steady_clock::now();
				auto elapsed_time =
					std::chrono::duration_cast<std::chrono::seconds>(
						end - begin
						).count();
				if (elapsed_time > max_time) {
					return timeout;
				}
				if (status == success) {
					encoder.extract_chain(spec, g, chain);
					fclose(fhandle);
					return success;
				}
			}
			fclose(fhandle);
			spec.nr_steps++;
		}

		return failure;
	}

	/// Synthesizes a chain using a set of serialized partial DAGs.
	inline synth_result pd_ser_synthesize_sorted(
		spec& spec,
		chain& chain,
		solver_wrapper& solver,
		partial_dag_encoder& encoder,
		bool fpi_new,
		std::string file_prefix = "",
		int max_time = std::numeric_limits<int>::max()) // Timeout in seconds
	{
		assert(spec.get_nr_in() >= spec.fanin);
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			chain.reset(spec.get_nr_in(), spec.get_nr_out(), 0, spec.fanin);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				chain.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}
		spec.nr_steps = spec.initial_steps;

		std::vector<std::string> dags_sorted;
		std::vector<int> vnr_dags;
		partial_dag g;
		if (fpi_new == false) {
			if (spec.nr_steps == 6) {
				dags_sorted.insert(dags_sorted.end(), { "pd5_6.bin","pd6_6.bin","pd6_7.bin",
					"pd7_6.bin","pd7_7.bin","pd7_8.bin","pd8_6.bin","pd8_7.bin","pd8_8.bin",
					"pd8_9.bin","pd9_6.bin","pd9_7.bin","pd9_8.bin","pd9_9.bin","pd9_10.bin" });
				vnr_dags.insert(vnr_dags.end(), { 13,116,43,964,581,143,8659,6671,2811,570,86855,78187,43411,15181,2303});
			}
			else if (spec.nr_steps == 5) {
				dags_sorted.insert(dags_sorted.end(), { "pd4_5.bin","pd5_5.bin","pd5_6.bin",
						"pd6_5.bin","pd6_6.bin","pd6_7.bin","pd7_5.bin","pd7_6.bin","pd7_7.bin","pd7_8.bin",
						"pd8_5.bin","pd8_6.bin","pd8_7.bin","pd8_8.bin","pd8_9.bin",
						"pd9_5.bin","pd9_6.bin","pd9_7.bin","pd9_8.bin","pd9_9.bin","pd9_9.bin","pd9_10.bin" });
				vnr_dags.insert(vnr_dags.end(), { 26,13,146,116,43,962,964,581,143,7463,8659,6671,2811,570,67443,86855,78187,43411,15181,2303 });
			}
		}
		else {
			std::vector<int> vmaxpi = {5,9,15,23,38,61};
			if (spec.nr_steps == 5) {
				for (int i = 4; i <= 9; i++) {
					for (int j = i; j < vmaxpi[i-4]; j++){
						std::string setname = "pd" + std::to_string(i) + '_' + std::to_string(j+1)+".bin";
						dags_sorted.insert(dags_sorted.end(), setname);
					}
				}
			}
		}


		auto begin = std::chrono::steady_clock::now();
		for (int pd_id = 0; pd_id < dags_sorted.size(); pd_id++) {
			spec.nr_steps = int(dags_sorted[pd_id][2]) - int('0');
			g.reset(2, int(dags_sorted[pd_id][2])-int('0'));
			const auto filename = file_prefix + dags_sorted[pd_id];
			auto fhandle = fopen(filename.c_str(), "rb");
			if (fhandle == NULL) {
				fprintf(stderr, "Error: unable to open file %s\n", filename.c_str());
				break;
			}

			int buf;
			int idx = 0;
			while (fread(&buf, sizeof(int), 1, fhandle) != 0) {
				idx++;
				for (int i = 0; i < spec.nr_steps; i++) {
					auto read = fread(&buf, sizeof(int), 1, fhandle);
					assert(read > 0);
					auto fanin1 = buf;
					read = fread(&buf, sizeof(int), 1, fhandle);
					assert(read > 0);
					auto fanin2 = buf;
					g.set_vertex(i, fanin1, fanin2);
				}

				if (!g.check_dag(spec.nr_in))
				{
					continue;
				}

				solver.restart();
				if (!encoder.encode(spec, g)) {
					continue;
				}
				const auto status = solver.solve(0);
				auto end = std::chrono::steady_clock::now();
				auto elapsed_time =
					std::chrono::duration_cast<std::chrono::seconds>(
						end - begin
						).count();
				if (elapsed_time > max_time) {
					return timeout;
				}
				if (status == success) {
					encoder.extract_chain(spec, g, chain);
					fclose(fhandle);
					return success;
				}
			}
			fclose(fhandle);
		}
		return failure;
	}

	/// Synthesizes a chain using a set of serialized partial DAGs.
	inline synth_result pd_ser_synthesize_sorted_parallel(
		spec& spec,
		chain& chain,
		solver_wrapper& solver,
		partial_dag_encoder& encoder,
		std::string file_prefix = "",
		int max_time = std::numeric_limits<int>::max()) // Timeout in seconds
	{
		assert(spec.get_nr_in() >= spec.fanin);
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			chain.reset(spec.get_nr_in(), spec.get_nr_out(), 0, spec.fanin);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				chain.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}
		std::vector<std::string> dags_sorted;
		std::vector<int> vnr_dags;
		dags_sorted.insert(dags_sorted.end(), { "pd5_6.bin","pd6_6.bin","pd6_7.bin",
			"pd7_6.bin","pd7_7.bin","pd7_8.bin","pd8_6.bin","pd8_7.bin","pd8_8.bin",
			"pd8_9.bin","pd9_6.bin","pd9_7.bin","pd9_8.bin","pd9_9.bin","pd9_10.bin" });
		vnr_dags.insert(vnr_dags.end(), { 13,116,43,964,581,143,8659,6671,2811,570,86855,78187,43411,15181,2303 });

		partial_dag g;
		std::vector<partial_dag> dags;
		spec.nr_steps = spec.initial_steps;

		auto begin = std::chrono::steady_clock::now();
		for (int pd_id = 0; pd_id < dags_sorted.size(); pd_id++) {
			spec.nr_steps = int(dags_sorted[pd_id][2]) - int('0');
			g.reset(2, int(dags_sorted[pd_id][2]) - int('0'));
			const auto filename = file_prefix + dags_sorted[pd_id];
			auto fhandle = fopen(filename.c_str(), "rb");
			if (fhandle == NULL) {
				fprintf(stderr, "Error: unable to open file %s\n", filename.c_str());
				break;
			}
			dags.clear();
			int buf;
			int idx = 0;

			while (fread(&buf, sizeof(int), 1, fhandle) != 0) {
				idx++;
				for (int i = 0; i < spec.nr_steps; i++) {
					auto read = fread(&buf, sizeof(int), 1, fhandle);
					assert(read > 0);
					auto fanin1 = buf;
					read = fread(&buf, sizeof(int), 1, fhandle);
					assert(read > 0);
					auto fanin2 = buf;
					g.set_vertex(i, fanin1, fanin2);
				}

				dags.push_back(g);
			}

			fclose(fhandle);
			synth_result res = pd_ser_synthesize_parallel(spec, chain, dags, vnr_dags[pd_id]);
			if (res == success) {
				return success;
			}
		}
		return failure;
	}

	/// Same as pd_ser_synthesize, but parallel.  
	inline synth_result pd_ser_synthesize_parallel(
		spec& spec,
		chain& c,
		int num_threads = std::thread::hardware_concurrency(),
		std::string file_prefix = "")
	{
		assert(spec.get_nr_in() >= spec.fanin);
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			c.reset(spec.get_nr_in(), spec.get_nr_out(), 0, spec.fanin);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				c.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		std::vector<std::thread> threads(num_threads);
		moodycamel::ConcurrentQueue<partial_dag> q(num_threads * 3);
		bool finished_generating = false;
		bool* pfinished = &finished_generating;
		int size_found = PD_SIZE_CONST;
		int* psize_found = &size_found;
		std::mutex found_mutex;

		for (int i = 0; i < num_threads; i++) {
			threads[i] = std::thread([&spec, psize_found, pfinished, &found_mutex, &c, &q] {
				percy::spec local_spec = spec;
				bsat_wrapper solver;
				partial_dag_encoder encoder(solver);
				partial_dag dag;

				while (*psize_found > local_spec.nr_steps) {
					if (!q.try_dequeue(dag)) {
						if (*pfinished) {
							std::this_thread::yield();
							if (!q.try_dequeue(dag)) {
								break;
							}
						}
						else {
							std::this_thread::yield();
							continue;
						}
					}
					local_spec.nr_steps = dag.nr_vertices();
					synth_result status;
					solver.restart();
					if (!encoder.encode(local_spec, dag)) {
						continue;
					}
					while (true) {
						status = solver.solve(10);
						if (status == failure) {
							break;
						}
						else if (status == success) {
							std::lock_guard<std::mutex> vlock(found_mutex);
							if (*psize_found > local_spec.nr_steps) {
								encoder.extract_chain(local_spec, dag, c);
								*psize_found = local_spec.nr_steps;
							}
							break;
						}
						else if (*psize_found <= local_spec.nr_steps) {
							// Another thread found a solution that's
							// better or equal to this one.
							break;
						}
					}
				}
				});
		}

		partial_dag g;
		spec.nr_steps = spec.initial_steps;
		while (size_found == PD_SIZE_CONST) {
			g.reset(2, spec.nr_steps);
			const auto filename = file_prefix + "pd" + std::to_string(spec.nr_steps) + ".bin";
			auto fhandle = fopen(filename.c_str(), "rb");
			if (fhandle == NULL) {
				fprintf(stderr, "Error: unable to open PD file\n");
				break;
			}

			int buf;
			while (fread(&buf, sizeof(int), 1, fhandle) != 0) {
				for (int i = 0; i < spec.nr_steps; i++) {
					auto read = fread(&buf, sizeof(int), 1, fhandle);
					assert(read > 0);
					auto fanin1 = buf;
					read = fread(&buf, sizeof(int), 1, fhandle);
					assert(read > 0);
					auto fanin2 = buf;
					g.set_vertex(i, fanin1, fanin2);
				}
				while (!q.try_enqueue(g)) {
					if (size_found == PD_SIZE_CONST) {
						std::this_thread::yield();
					}
					else {
						break;
					}
				}
				if (size_found != PD_SIZE_CONST) {
					break;
				}
			}
			fclose(fhandle);
			spec.nr_steps++;
		}
		finished_generating = true;
		for (auto& thread : threads) {
			thread.join();
		}
		spec.nr_steps = size_found;

		return size_found == PD_SIZE_CONST ? failure : success;
	}

	/// Same as pd_ser_synthesize, but parallel.  
	inline synth_result pd_ser_synthesize_parallel(
		spec& spec,
		chain& c,
		std::vector<partial_dag> dags,
		int nr_dag)
	{
		int num_threads = std::thread::hardware_concurrency();
		std::vector<std::thread> threads(num_threads);
		moodycamel::ConcurrentQueue<partial_dag> q(num_threads * 3);
		bool finished_generating = false;
		bool* pfinished = &finished_generating;
		int size_found = PD_SIZE_CONST;
		int* psize_found = &size_found;
		std::mutex found_mutex;

		for (int i = 0; i < num_threads; i++) {
			threads[i] = std::thread([&spec, psize_found, pfinished, &found_mutex, &c, &q] {
				percy::spec local_spec = spec;
				bsat_wrapper solver;
				partial_dag_encoder encoder(solver);
				partial_dag dag;
				local_spec.nr_steps = 0;

				while (*psize_found > local_spec.nr_steps) {
					if (!q.try_dequeue(dag)) {
						if (*pfinished) {
							std::this_thread::yield();
							if (!q.try_dequeue(dag)) {
								break;
							}
						}
						else {
							std::this_thread::yield();
							continue;
						}
					}
					local_spec.nr_steps = dag.nr_vertices();
					synth_result status;
					solver.restart();
					if (!encoder.encode(spec, dag)) {
						continue;
					}
					while (true) {
						status = solver.solve(10);
						if (status == failure) {
							break;
						}
						else if (status == success) {
							std::lock_guard<std::mutex> vlock(found_mutex);
							if (*psize_found > local_spec.nr_steps) {
								encoder.extract_chain(spec, dag, c); // clauses to boolean chain
								*psize_found = local_spec.nr_steps;
							}
							break;
						}
						else if (*psize_found <= local_spec.nr_steps) {
							// Another thread found a solution that's
							// better or equal to this one.
							break;
						}

					}
				}
				});
		}
		size_t dag_idx = 0;
		while (size_found == PD_SIZE_CONST) {
			while (!q.try_enqueue(dags[dag_idx])) {
				if (size_found == PD_SIZE_CONST) {
					std::this_thread::yield();
				}
				else {
					break;
				}
			}
			if (dag_idx + 1 == nr_dag) {
				break;
			}
			dag_idx++;
		}
		finished_generating = true;
		for (auto& thread : threads) {
			thread.join();
		}

		return size_found == PD_SIZE_CONST ? failure : success;
	}

	inline synth_result
		pf_fence_synthesize(
			spec& spec,
			chain& c,
			int num_threads = std::thread::hardware_concurrency())
	{
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			c.reset(spec.get_nr_in(), spec.get_nr_out(), 0, spec.fanin);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				c.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		std::vector<std::thread> threads(num_threads);

		moodycamel::ConcurrentQueue<fence> q(num_threads * 3);

		bool finished_generating = false;
		bool* pfinished = &finished_generating;
		bool found = false;
		bool* pfound = &found;
		std::mutex found_mutex;

		spec.nr_steps = spec.initial_steps;
		while (true) {
			for (int i = 0; i < num_threads; i++) {
				threads[i] = std::thread([&spec, pfinished, pfound, &found_mutex, &c, &q] {
					bsat_wrapper solver;
					ssv_fence2_encoder encoder(solver);
					fence local_fence;

					while (!(*pfound)) {
						if (!q.try_dequeue(local_fence)) {
							if (*pfinished) {
								std::this_thread::yield();
								if (!q.try_dequeue(local_fence)) {
									break;
								}
							}
							else {
								std::this_thread::yield();
								continue;
							}
						}
						synth_result status;
						solver.restart();
						if (!encoder.encode(spec, local_fence)) {
							continue;
						}
						do {
							status = solver.solve(10);
							if (*pfound) {
								break;
							}
							else if (status == success) {
								std::lock_guard<std::mutex> vlock(found_mutex);
								if (!(*pfound)) {
									encoder.extract_chain(spec, c);
									*pfound = true;
								}
							}
						} while (status == timeout);
					}
				});
			}
			generate_fences(spec, q);
			finished_generating = true;

			for (auto& thread : threads) {
				thread.join();
			}
			if (found) {
				break;
			}
			finished_generating = false;
			spec.nr_steps++;
			std::cout << printf("step number: %d\n", spec.nr_steps);
			if (spec.nr_steps > 8) {
				return failure;
			}
		}
		return success;
	}

	inline synth_result
		pf_fence_synthesize_givennf_classic_new(
			std::vector<spec>& spec_all,
			std::vector<chain>& c,
			fence local_fence0,
			int num_threads = std::thread::hardware_concurrency())
	{

		for (int i = 1; i < spec_all.size(); i++) { // verify if the input number equals
			assert(spec_all[i - 1].nr_in == spec_all[i].nr_in);
		}
		for (int i = 0; i < spec_all.size(); i++) { // preprocess
			spec_all[i].preprocess();
		}

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		for (int i = 0; i < spec_all.size(); i++) {
			if (spec_all[i].nr_triv == spec_all[i].get_nr_out()) {
				c[0].reset(spec_all[i].get_nr_in(), spec_all[i].get_nr_out(), 0, spec_all[i].fanin);
				for (int h = 0; h < spec_all[i].get_nr_out(); h++) {
					c[0].set_output(h, (spec_all[i].triv_func(h) << 1) +
						((spec_all[i].out_inv >> h) & 1));
				}
				return success;
			}
		}

		std::vector<std::thread> threads(num_threads);

		moodycamel::ConcurrentQueue<fence> q(num_threads * 2);

		bool finished_generating = false;
		bool* pfinished = &finished_generating;
		bool found = false;
		bool* pfound = &found;
		std::mutex found_mutex;

		spec_all[0].nr_steps = spec_all[0].initial_steps; // initialize step number
		spec_all[1].nr_steps = spec_all[1].initial_steps;
		while (true) {
			for (int i = 0; i < num_threads; i++) {
				threads[i] = std::thread([&spec_all, pfinished, pfound, &found_mutex, &c, &q] {
					bsat_wrapper solver;
					ssv_fence2_encoder encoder(solver);
					fence local_fence;

					while (!(*pfound)) { // break if synthesis succeed
						if (!q.try_dequeue(local_fence)) {
							if (*pfinished) {
								std::this_thread::yield();
								if (!q.try_dequeue(local_fence)) {
									break;
								}
							}
							else {
								std::this_thread::yield();
								continue;
							}
						}
						synth_result status;
						solver.restart();
						if (!encoder.encode_nc(spec_all, local_fence)) { // encode fence and truth table to clauses
							continue;
						}
						do {
							status = solver.solve(10);
							if (*pfound) {
								break;
							}
							else if (status == success) {
								std::lock_guard<std::mutex> vlock(found_mutex);
								if (!(*pfound)) {
									for (int ispec = 0; ispec < spec_all.size(); ispec++) {
										encoder.extract_chain_nc(spec_all[ispec], c[ispec], ispec); // clauses to boolean chain
									}
									*pfound = true;
								}
							}
						} while (status == timeout);
					}
					});
			}
			//generate_fences_new(spec_all[0], q, local_fence0); // give a fence by user
			generate_fences(spec_all[0], q);
			//generate_fences(spec_all[1], q);
			finished_generating = true;

			for (auto& thread : threads) {
				thread.join();
			}
			if (found) {
				break;
			}
			finished_generating = false;
			spec_all[0].nr_steps++;
			spec_all[1].nr_steps++;
			std::cout << printf("step number: %d\n", spec_all[0].nr_steps);
			if (spec_all[0].nr_steps > 9) {
				return failure;
			}
		}
		return success;
	}

	inline synth_result
		pf_fence_synthesize_givennf_classic(
			std::vector<spec>& spec_all,
			std::vector<chain>& c,
			int& nfences,
			int num_threads = 1)
			//int num_threads = std::thread::hardware_concurrency())
	{

		for (int i = 1; i < spec_all.size(); i++) { // verify if the input number equals
			assert(spec_all[i - 1].nr_in == spec_all[i].nr_in);
		}
		for (int i = 0; i < spec_all.size(); i++) { // preprocess
			spec_all[i].preprocess();
		}

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		for (int i = 0; i < spec_all.size(); i++) {
			if (spec_all[i].nr_triv == spec_all[i].get_nr_out()) {
				c[0].reset(spec_all[i].get_nr_in(), spec_all[i].get_nr_out(), 0, spec_all[i].fanin);
				for (int h = 0; h < spec_all[i].get_nr_out(); h++) {
					c[0].set_output(h, (spec_all[i].triv_func(h) << 1) +
						((spec_all[i].out_inv >> h) & 1));
				}
				return success;
			}
		}

		std::vector<std::thread> threads(num_threads);

		moodycamel::ConcurrentQueue<fence> q(num_threads * 1);

		bool finished_generating = false;
		bool* pfinished = &finished_generating;
		bool found = false;
		bool* pfound = &found;
		std::mutex found_mutex;
		int* pnfences = &nfences;
		std::mutex nfences_mutex;

		/*
		spec_all[0].nr_steps = spec_all[0].initial_steps; // initialize step number
		spec_all[1].nr_steps = spec_all[1].initial_steps;
		*/
		spec_all[0].nr_steps = 5; // initialize step number
		spec_all[1].nr_steps = 5;
		while (true) {
			for (int i = 0; i < num_threads; i++) {
				//for (int i = 0; i < 1; i++) {
				threads[i] = std::thread([&spec_all, pfinished, pfound, &found_mutex, &c, &q, pnfences, &nfences_mutex] {
					bsat_wrapper solver;
					ssv_fence2_encoder encoder(solver);
					fence local_fence;
					int restarttimes1 = 0;
					while (!(*pfound)) { // break if synthesis succeed
						if (!q.try_dequeue(local_fence)) {
							if (*pfinished) {
								std::this_thread::yield();
								if (!q.try_dequeue(local_fence)) {
									break;
								}
							}
							else {
								std::this_thread::yield();
								continue;
							}
						}
						{
							std::lock_guard<std::mutex> vlock(nfences_mutex);
							(*pnfences)++;
						}
						synth_result status;
						solver.restart();
						int restarttimes2 = 0;
						if (!encoder.encode_nc(spec_all, local_fence)) { // encode fence and truth table to clauses
							continue;
						}
						do {
							status = solver.solve(10);
							restarttimes1++;
							restarttimes2++;
							/*
							if ((*pfound==true) && (status != success)) {
								{
									std::lock_guard<std::mutex> vlock(nfences_mutex);
									(*pnfences)--;
								}
								break;
							}*/
							if (*pfound) {
								break;
							}
							else if (status == success) {
								std::lock_guard<std::mutex> vlock(found_mutex);
								if (!(*pfound)) {
									for (int ispec = 0; ispec < spec_all.size(); ispec++) {
										encoder.extract_chain_nc(spec_all[ispec], c[ispec], ispec); // clauses to boolean chain
									}
									*pfound = true;
								}
							}
						} while (status == timeout);
					}
				});
			}
			generate_fences(spec_all[0], q);
			//generate_fences(spec_all[1], q);
			finished_generating = true;

			for (auto& thread : threads) {
				thread.join();
			}
			if (found) {
				break;
			}
			finished_generating = false;
			spec_all[0].nr_steps++;
			spec_all[1].nr_steps++;
			std::cout << printf("step number: %d\n", spec_all[0].nr_steps);
			if (spec_all[0].nr_steps > 9) {
				return failure;
			}
		}
		return success;
	}

	inline synth_result
		pf_fence_synthesize_givennf_classic_abc(
			std::vector<spec>& spec_all,
			std::vector < std::vector<chain>>& c_all,
			unsigned nr_levels_max,
			int num_threads = std::thread::hardware_concurrency()
			//int num_threads = 1
		)
	{
		//std::vector<chain> c = c_all[c_all.size() - 1];
		chain c0;
		std::vector<chain> c;
		c.push_back(c0);
		c.push_back(c0);
		int nnode_max = 8;

		for (int i = 1; i < spec_all.size(); i++) { // verify if the input number equals
			assert(spec_all[i - 1].nr_in == spec_all[i].nr_in);
		}
		for (int i = 0; i < spec_all.size(); i++) { // preprocess
			spec_all[i].preprocess();
		}

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		for (int i = 0; i < spec_all.size(); i++) {
			if (spec_all[i].nr_triv == spec_all[i].get_nr_out()) {
				c[0].reset(spec_all[i].get_nr_in(), spec_all[i].get_nr_out(), 0, spec_all[i].fanin);
				for (int h = 0; h < spec_all[i].get_nr_out(); h++) {
					c[0].set_output(h, (spec_all[i].triv_func(h) << 1) +
						((spec_all[i].out_inv >> h) & 1));
				}
				//c_all[c_all.size() - 1] = c;
				return success;
			}
		}

		std::vector<std::thread> threads(num_threads);

		moodycamel::ConcurrentQueue<fence> q(num_threads * 3);
		//moodycamel::ConcurrentQueue<fence> q(num_threads * 1);

		bool finished_generating = false;
		bool* pfinished = &finished_generating;
		//bool found = false;
		//bool* pfound = &found;
		//std::mutex found_mutex;
		int nr_node_max = nnode_max;
		int* pnr_node_max = &nr_node_max;
		bool nextfence = true;
		int fended = 0;
		int* pfended = &fended;
		std::mutex fended_mutex;
		std::vector < std::vector<chain>>* pc_all = &c_all;
		std::mutex pc_all_mutex;




		/*spec_all[0].nr_steps = spec_all[0].initial_steps; // initialize step number
		spec_all[1].nr_steps = spec_all[1].initial_steps;
		*/
		spec_all[0].nr_steps = 4; // initialize step number
		spec_all[1].nr_steps = 4;
		while (true) {
			for (int i = 0; i < num_threads; i++) {
				//for (int i = 0; i < 1; i++) {
				threads[i] = std::thread([&spec_all, &c_all, &pc_all_mutex, pfinished, &q, &c, pnr_node_max, pfended, &fended_mutex] {
					bsat_wrapper solver;
					ssv_fence2_encoder encoder(solver);
					fence local_fence;
					int restarttimes1 = 0;

					//while (!(*pfound)) { // break if synthesis succeed
					while (spec_all[0].nr_steps <= *pnr_node_max) { // break if synthesis succeed
						if (!q.try_dequeue(local_fence)) { // check if fences in the queue is out
							if (*pfinished) {
								std::this_thread::yield();
								if (!q.try_dequeue(local_fence)) {
									break;
								}
							}
							else {
								std::this_thread::yield();
								continue;
							}
						}

						synth_result status;
						//chain c0;
						std::vector <chain> c_;
						c_ = c;
						std::vector < std::vector <chain>> c_fence;
						//c_.push_back(c0);
						//c_.push_back(c0);
						std::vector<std::vector <int>> rez;
						bool found_ = false;

						unsigned fquit = 0;
						{
							std::lock_guard<std::mutex> vlock(fended_mutex);
							(*pfended)++;
						}
						do {
							solver.restart();
							int restarttimes2 = 0;
							if (!encoder.encode_nc_abc(spec_all, local_fence, rez)) { // encode fence and truth table to clauses
								break;
							}
							do {
								status = solver.solve(10);
								restarttimes1++;
								restarttimes2++;
								if (status == failure) {
									break;
								}
								else if (status == success) {
									//std::lock_guard<std::mutex> vlock(found_mutex);
									//if (!(found_)) {
									if (true) {
										for (int ispec = 0; ispec < spec_all.size(); ispec++) {
											encoder.extract_chain_nc(spec_all[ispec], c_[ispec], ispec, rez); // clauses to boolean chain
										}
										found_ = true; // never report success, only report failure
									}
								}
							} while (status == timeout);
							if (status == success) {
								c_fence.push_back(c_);
							}
							if (c_fence.size()==2){
								std::vector <int> comp_var = encoder.compare_vars(rez[0], rez[1]);
								if (comp_var.size()==0)
								{
									assert(false);
								}
								if (encoder.compare_boolean_chain(c_fence[0][0], c_fence[1][0])==failure 
									&& encoder.compare_boolean_chain(c_fence[0][1], c_fence[1][1]) == failure)
								{
									assert(false);
								}
								/*if (encoder.compare_boolean_chain(c_fence[0][1], c_fence[1][1]) == failure)
								{
									break;
								}*/
							}
						} while (status != failure && rez.size() < 10);
						if (c_fence.size() > 0) {
							std::lock_guard<std::mutex> vlock(pc_all_mutex);
							for (int icf = 0; icf < c_fence.size(); ++icf) {
								auto sim_fs_f1 = c_fence[icf][0].simulate();
								auto sim_fs_f2 = c_fence[icf][1].simulate();
								if (!(sim_fs_f1[0] == spec_all[0][0]))
									continue;
								if (!(sim_fs_f2[0] == spec_all[1][0]))
									continue;
								c_all.push_back(c_fence[icf]);
							}
						}
						{
							std::lock_guard<std::mutex> vlock(fended_mutex);
							(*pfended)--;
						}
					}
					});
			}
			if (spec_all[0].nr_steps <= *pnr_node_max)
				std::cout << printf("Process with step number: %d\n", spec_all[0].nr_steps);
			if (c_all.size() > 0)
				*pnr_node_max = min(c_all[0][0].get_nr_steps()+2, *pnr_node_max);
			generate_fences_abc(spec_all[0], q, nr_levels_max);
			//generate_fences(spec_all[1], q);
			finished_generating = true;

			for (auto& thread : threads) {
				thread.join();
			}
			/*if (found) {
				break;
			}*/
			if (spec_all[0].nr_steps >= *pnr_node_max) {
				while (*pfended != 0) {
					this_thread::sleep_for(chrono::microseconds(3000));
				}
				if (c_all.size() == 0)
					this_thread::sleep_for(chrono::microseconds(1));
				break;
			}
			finished_generating = false;
			spec_all[0].nr_steps++;
			spec_all[1].nr_steps++;

			if (spec_all[0].nr_steps > nnode_max && c_all.size() < 1) {
				return failure;
			}
		}
		return success;
	}

	inline synth_result
		pf_fence_synthesize_givenf(
			spec& spec1,
			chain& c,
			fence local_fence)
	{
		spec1.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec1.nr_triv == spec1.get_nr_out()) {
			c.reset(spec1.get_nr_in(), spec1.get_nr_out(), 0, spec1.fanin);
			for (int h = 0; h < spec1.get_nr_out(); h++) {
				c.set_output(h, (spec1.triv_func(h) << 1) +
					((spec1.out_inv >> h) & 1));
			}
			return success;
		}

		bsat_wrapper solver;
		ssv_fence2_encoder encoder(solver);
		synth_result status;
		solver.restart();
		if (!encoder.encode(spec1, local_fence)) {
			assert(1 == 0);
		}
		status = solver.solve(0);

		if (status == success) {
			encoder.extract_chain(spec1, c);
			if (spec1.verbosity > 2) {
				//    encoder.print_solver_state(spec);
			}
			return success;
		}
		else if (status == failure) {
			return failure;
		}
		else {
			return percy::synth_result::timeout;
		}
	}

	inline synth_result
		pf_fence_synthesize_given2f(
			spec& spec1,
			spec& spec2,
			chain& c1,
			chain& c2,
			fence local_fence)
	{
		assert(spec1.nr_in == spec2.nr_in);
		spec1.preprocess();
		spec2.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec1.nr_triv == spec1.get_nr_out()) {
			c1.reset(spec1.get_nr_in(), spec1.get_nr_out(), 0, spec1.fanin);
			for (int h = 0; h < spec1.get_nr_out(); h++) {
				c1.set_output(h, (spec1.triv_func(h) << 1) +
					((spec1.out_inv >> h) & 1));
			}
			return success;
		}
		if (spec2.nr_triv == spec2.get_nr_out()) {
			c2.reset(spec2.get_nr_in(), spec2.get_nr_out(), 0, spec2.fanin);
			for (int h = 0; h < spec2.get_nr_out(); h++) {
				c2.set_output(h, (spec2.triv_func(h) << 1) +
					((spec2.out_inv >> h) & 1));
			}
			return success;
		}

		bsat_wrapper solver;
		ssv_fence2_encoder encoder(solver);
		synth_result status;
		solver.restart();
		if (!encoder.encode_2c(spec1, spec2, local_fence)) {
			assert(1 == 0);
		}
		status = solver.solve(0);

		if (status == success) {
			encoder.extract_chain(spec1, c1);
			encoder.extract_chain_2c(spec2, c2);
			if (spec1.verbosity > 2) {
				//    encoder.print_solver_state(spec);
			}
			return success;
		}
		else if (status == failure) {
			return failure;
		}
		else {
			return percy::synth_result::timeout;
		}
	}



	inline synth_result
		pf_fence_synthesize_givennf(
			std::vector<spec>& spec_all,
			std::vector<chain>& c,
			fence local_fence)
	{
		for (int i = 1; i < spec_all.size(); i++) {
			assert(spec_all[i - 1].nr_in == spec_all[i].nr_in);
		}
		for (int i = 0; i < spec_all.size(); i++) {
			spec_all[i].preprocess();
		}

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		for (int i = 0; i < spec_all.size(); i++) {
			if (spec_all[i].nr_triv == spec_all[i].get_nr_out()) {
				c[0].reset(spec_all[i].get_nr_in(), spec_all[i].get_nr_out(), 0, spec_all[i].fanin);
				for (int h = 0; h < spec_all[i].get_nr_out(); h++) {
					c[0].set_output(h, (spec_all[i].triv_func(h) << 1) +
						((spec_all[i].out_inv >> h) & 1));
				}
				return success;
			}
		}


		spec_all[0].nr_steps = local_fence.nr_nodes(); // initialize step number
		spec_all[1].nr_steps = local_fence.nr_nodes();
		bsat_wrapper solver;
		ssv_fence2_encoder encoder(solver);
		synth_result status;
		solver.restart();

		if (!encoder.encode_nc(spec_all, local_fence)) {
			assert(1 == 0);
		}
		status = solver.solve(10);

		if (status == success) {
			for (int ispec = 0; ispec < spec_all.size(); ispec++) {
				encoder.extract_chain_nc(spec_all[ispec], c[ispec], ispec);
			}
			if (spec_all[0].verbosity > 2) {
				//    encoder.print_solver_state(spec);
			}
			return success;
		}
		else if (status == failure) {
			return failure;
		}
		else {
			return percy::synth_result::timeout;
		}
	}

	inline synth_result
		pf_fence_synthesize_givennf_new(
			std::vector<spec>& spec_all,
			std::vector<chain>& c,
			fence local_fence)
	{
		for (int i = 1; i < spec_all.size(); i++) {
			assert(spec_all[i - 1].nr_in == spec_all[i].nr_in);
		}
		for (int i = 0; i < spec_all.size(); i++) {
			spec_all[i].preprocess();
		}

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		for (int i = 0; i < spec_all.size(); i++) {
			if (spec_all[i].nr_triv == spec_all[i].get_nr_out()) {
				c[0].reset(spec_all[i].get_nr_in(), spec_all[i].get_nr_out(), 0, spec_all[i].fanin);
				for (int h = 0; h < spec_all[i].get_nr_out(); h++) {
					c[0].set_output(h, (spec_all[i].triv_func(h) << 1) +
						((spec_all[i].out_inv >> h) & 1));
				}
				return success;
			}
		}


		spec_all[0].nr_steps = local_fence.nr_nodes(); // initialize step number
		spec_all[1].nr_steps = local_fence.nr_nodes();
		bsat_wrapper solver;
		ssv_fence2_encoder encoder(solver);
		synth_result status;
		solver.restart();

		if (!encoder.encode_nc(spec_all, local_fence)) {
			assert(1 == 0);
		}
		do {
			status = solver.solve(10);

			if (status == success) {
				for (int ispec = 0; ispec < spec_all.size(); ispec++) {
					encoder.extract_chain_nc(spec_all[ispec], c[ispec], ispec);
				}
				if (spec_all[0].verbosity > 2) {
					//    encoder.print_solver_state(spec);
				}
				return success;
			}
			else if (status == failure) {
				return failure;
			}
		} while (status == timeout);
		/*else {
			return percy::synth_result::timeout;
		}*/
	}

	inline synth_result
		parallel_pf_fence_synthesize_givennf(
			std::vector<spec>& spec_all,
			std::vector<chain>& c,
			fence local_fence,
			int num_threads = std::thread::hardware_concurrency())
	{
		for (int i = 1; i < spec_all.size(); i++) {
			assert(spec_all[i - 1].nr_in == spec_all[i].nr_in);
		}
		for (int i = 0; i < spec_all.size(); i++) {
			spec_all[i].preprocess();
		}

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		for (int i = 0; i < spec_all.size(); i++) {
			if (spec_all[i].nr_triv == spec_all[i].get_nr_out()) {
				c[0].reset(spec_all[i].get_nr_in(), spec_all[i].get_nr_out(), 0, spec_all[i].fanin);
				for (int h = 0; h < spec_all[i].get_nr_out(); h++) {
					c[0].set_output(h, (spec_all[i].triv_func(h) << 1) +
						((spec_all[i].out_inv >> h) & 1));
				}
				return success;
			}
		}

		std::vector<std::thread> threads(num_threads);

		moodycamel::ConcurrentQueue<fence> q(num_threads * 3);

		bool finished_generating = false;
		bool* pfinished = &finished_generating;
		bool found = false;
		bool* pfound = &found;
		std::mutex found_mutex;
		int nr_addnode = 0;
		auto current_nr_level = local_fence.nr_levels();
		spec_all[0].nr_steps = local_fence.nr_nodes(); // initialize step number
		spec_all[1].nr_steps = local_fence.nr_nodes();
		while (true) {
			for (int i = 0; i < num_threads; i++) {
				threads[i] = std::thread([&spec_all, pfinished, pfound, &found_mutex, &c, &q] {
					bsat_wrapper solver;
					ssv_fence2_encoder encoder(solver);
					fence local_fence;

					while (!(*pfound)) {
						if (!q.try_dequeue(local_fence)) {
							if (*pfinished) {
								std::this_thread::yield();
								if (!q.try_dequeue(local_fence)) {
									break;
								}
							}
							else {
								std::this_thread::yield();
								continue;
							}
						}
						synth_result status;
						solver.restart();
						if (!encoder.encode_nc(spec_all, local_fence)) {
							continue;
						}
						do {
							status = solver.solve(0);
							if (*pfound) {
								break;
							}
							else if (status == success) {
								std::lock_guard<std::mutex> vlock(found_mutex);
								if (!(*pfound)) {
									for (int ispec = 0; ispec < spec_all.size(); ispec++) {
										encoder.extract_chain_nc(spec_all[ispec], c[ispec], ispec);
									}
									*pfound = true;
								}
							}
						} while (status == timeout);
					}
					});
			}
			//generate_fences(spec, q);
			fence new_fence = local_fence;
			if (nr_addnode == 0) {
				while (!q.try_enqueue(local_fence)) {
					std::this_thread::yield();
				}
			}
			else {
				auto nr_addnode1 = nr_addnode;
				auto nr_addnode2 = nr_addnode;
				auto fixnode = 0;
				for (int i = 0; i < current_nr_level - local_fence.nr_levels(); i++) {
					fixnode = fixnode + (local_fence.nr_levels() + i);
				}

				if (nr_addnode1 - fixnode == current_nr_level + 1) { // add one level if all layer has been fullfilled a round
					current_nr_level++;
					new_fence.reset(new_fence.nr_nodes() + 1, current_nr_level);
					//for (int i = 0; i < local_fence.nr_levels(); i++)
						//new_fence[i] = local_fence[i];
					new_fence[current_nr_level - 1]++;

				}
				else {
					new_fence.reset(new_fence.nr_nodes(), current_nr_level);
					for (int i = 0; i < current_nr_level - local_fence.nr_levels(); i++) {
						new_fence[current_nr_level - 1 - i]++;
						new_fence.set_nr_node(new_fence.nr_nodes() + 1);
					}
				}

				nr_addnode1 = nr_addnode1 - current_nr_level + local_fence.nr_levels();
				//new_fence.set_nr_node(new_fence.nr_nodes() - current_nr_level + local_fence.nr_levels());
				for (int i = 0; i < floor((nr_addnode1 - 1) / new_fence.nr_levels()); i++) { // fullfill all layers in rounds
					for (int j = 0; j < new_fence.nr_levels(); j++) {
						new_fence[j]++;
						new_fence.set_nr_node(new_fence.nr_nodes() + 1);
					}
				}
				for (int i = 0; i < nr_addnode1 - 1 - floor((nr_addnode1 - 1) / new_fence.nr_levels()) * new_fence.nr_levels(); i++) { // fill the fixed nodes
					new_fence[i]++;
					new_fence.set_nr_node(new_fence.nr_nodes() + 1);
				}

				if (nr_addnode2 - fixnode == current_nr_level) {
					fence new_fence2 = local_fence;
					new_fence2[new_fence2.nr_levels() - 1]++;
					while (!q.try_enqueue(new_fence)) {
						std::this_thread::yield();
					}
				}
				find_new_fences(new_fence, q); // fill one flexible node
			}
			finished_generating = true;

			for (auto& thread : threads) {
				thread.join();
			}
			if (found) {
				break;
			}
			finished_generating = false;
			nr_addnode++;
			if (nr_addnode >= spec_all.size() * local_fence.nr_nodes()) {
				return failure;
			}
		}
		return success;
	}

	/*inline void
		find_new_fences(fence& local_fence, moodycamel::ConcurrentQueue<fence>& q)
	{
		rec_fence_generator gen;

		for (int l = 1; l <= spec.nr_steps; l++) {
			gen.reset(spec.nr_steps, l, spec.get_nr_out(), spec.fanin);
			gen.generate_fences(q);
		}
	}
	void
		generate_fences(moodycamel::ConcurrentQueue<fence>& q)
	{
		assert(_initialized);
		_callback = [&q](rec_fence_generator* gen) {
			const auto nr_levels = gen->nr_levels();
			fence f(gen->nr_nodes(), nr_levels);
			for (int i = 0; i < nr_levels; i++) {
				f[i] = gen->nodes_on_level(nr_levels - 1 - i);
			}
			while (!q.try_enqueue(f)) {
				std::this_thread::yield();
			}
		};
		search_fences();
		_callback = 0;
		_initialized = false;
	}*/

	inline fence find_new_fence1(const int nr_try, fence f0) { // evenly add node, do not add level
		int nr_level = f0.nr_levels();
		int add_nr = floor(nr_try / nr_level);
		f0.set_nr_node(f0.nr_nodes() + add_nr + 1);
		f0[(nr_try) % nr_level]++; // add flexible new node
		for (int i = 0; i < add_nr; i++) { // add fixed new node
			f0[i % nr_level]++;
		}
		return f0;
	}
	/*struct return_pack {
		int add_node, flt_node;
		fence f0;
	};
	inline fence find_new_fence2(const int nr_try, const int add_node, const int flt_node, fence f0) { // evenly add node, add level
		struct return_pack;
		return_pack.add_node = add_node;

		return f0, add_node, flt_node;
	}*/

	inline fence find_new_fence2(const int nr_try, fence f0) { // evenly add node, add level
		int ilevel = 0;
		for (int i = 0; i <= nr_try; i++) {
			f0.set_nr_node(f0.nr_nodes() + 1);
			if (ilevel < f0.nr_levels()) {
				f0[ilevel]++;
				ilevel++;
				//f0[(nr_try) % f0.nr_levels()]++;
			}
			else {
				f0.reset(f0.nr_nodes(), f0.nr_levels() + 1);
				int testpin = f0.nr_levels() - 1;
				f0[f0.nr_levels() - 1]++;
				ilevel = 0;
			}
		}
		return f0;
	}

	inline fence find_new_fence3(const int nr_try, fence f0) { // add more in lower level
		int maxlevel = 0;
		int nodeadded = 0;
		while (1) {
			maxlevel++;
			for (int ilevel = 0; ilevel < maxlevel; ilevel++) {
				if (nodeadded < nr_try + 1) {
					f0.set_nr_node(f0.nr_nodes() + 1);
					nodeadded++;
					f0[ilevel]++;
				}
				else {
					return f0;
				}
			}
		}
		return f0;
	}

	inline fence find_new_fence4(const int nr_try, fence f0) { // add more in higher level
		int maxlevel = 0;
		int nodeadded = 0;
		while (1) {
			maxlevel++;
			for (int ilevel = 0; ilevel < maxlevel; ilevel++) {
				if (nodeadded < nr_try + 1) {
					f0.set_nr_node(f0.nr_nodes() + 1);
					nodeadded++;
					f0[f0.nr_levels() - 1 - ilevel]++;
				}
				else {
					return f0;
				}
			}
		}
		return f0;
	}

	inline synth_result
		pf_fence_synthesize_given2f2(
			spec& spec1,
			spec& spec2,
			chain& c1,
			chain& c2,
			fence local_fence)
	{
		assert(spec1.nr_in == spec2.nr_in);
		spec1.preprocess();
		spec2.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec1.nr_triv == spec1.get_nr_out()) {
			c1.reset(spec1.get_nr_in(), spec1.get_nr_out(), 0, spec1.fanin);
			for (int h = 0; h < spec1.get_nr_out(); h++) {
				c1.set_output(h, (spec1.triv_func(h) << 1) +
					((spec1.out_inv >> h) & 1));
			}
			return success;
		}
		if (spec2.nr_triv == spec2.get_nr_out()) {
			c2.reset(spec2.get_nr_in(), spec2.get_nr_out(), 0, spec2.fanin);
			for (int h = 0; h < spec2.get_nr_out(); h++) {
				c2.set_output(h, (spec2.triv_func(h) << 1) +
					((spec2.out_inv >> h) & 1));
			}
			return success;
		}

		spec1.nr_steps = local_fence.nr_nodes(); // initialize step number
		spec2.nr_steps = local_fence.nr_nodes();
		bsat_wrapper solver;
		ssv_fence2_encoder encoder(solver);
		synth_result status;
		solver.restart();
		if (!encoder.encode_2c(spec1, spec2, local_fence)) {
			assert(1 == 0);
		}
		status = solver.solve(0);

		if (status == success) {
			encoder.extract_chain(spec1, c1);
			encoder.extract_chain_2c(spec2, c2);
			if (spec1.verbosity > 2) {
				//    encoder.print_solver_state(spec);
			}
			return success;
		}
		else if (status == failure) {
			return failure;
		}
		else {
			return percy::synth_result::timeout;
		}
	}

	/// Performs fence-based parallel synthesis.
	/// One thread generates fences and places them on a concurrent
	/// queue. The remaining threads dequeue fences and try to
	/// synthesize chains with them.
	inline synth_result
		pf_synthesize(
			spec& spec,
			chain& chain,
			SynthMethod synth_method = SYNTH_FENCE)
	{
		switch (synth_method) {
		case SYNTH_FENCE:
			return pf_fence_synthesize(spec, chain);
			//        case SYNTH_FENCE_CEGAR:
			//            return pf_fence_cegar_synthesize(spec, chain, solver, encoder);
		default:
			fprintf(stderr, "Error: synthesis method %d not supported\n", synth_method);
			exit(1);
		}
	}

	inline synth_result
		synthesize(
			spec& spec,
			chain& chain,
			SolverType slv_type = SLV_BSAT2,
			EncoderType enc_type = ENC_SSV,
			SynthMethod method = SYNTH_STD)
	{
		auto solver = get_solver(slv_type);
		auto encoder = get_encoder(*solver, enc_type);
		return synthesize(spec, chain, *solver, *encoder, method);
	}

	inline synth_result
		synthesize_cegar(
			spec& spec,
			chain& chain,
			SolverType slv_type = SLV_BSAT2,
			EncoderType enc_type = ENC_SSV,
			SynthMethod method = SYNTH_FENCE_CEGAR)
	{
		auto solver = get_solver(slv_type);
		auto encoder = get_encoder(*solver, enc_type);
		return synthesize(spec, chain, *solver, *encoder, method);
	}

	inline synth_result
		next_solution(
			spec& spec,
			chain& chain,
			solver_wrapper& solver,
			enumerating_encoder& encoder,
			SynthMethod synth_method = SYNTH_STD)
	{
		if (!encoder.is_dirty()) {
			encoder.set_dirty(true);
			switch (synth_method) {
			case SYNTH_STD:
			case SYNTH_STD_CEGAR:
				return std_synthesize(spec, chain, solver, dynamic_cast<std_encoder&>(encoder));
			case SYNTH_FENCE:
				return fence_synthesize(spec, chain, solver, dynamic_cast<fence_encoder&>(encoder));
			default:
				fprintf(stderr, "Error: solution enumeration not supported for synth method %d\n", synth_method);
				exit(1);
			}
		}

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		// In this case, only one solution exists.
		if (spec.nr_triv == spec.get_nr_out()) {
			return failure;
		}

		if (encoder.block_solution(spec)) {
			const auto status = solver.solve(spec.conflict_limit);

			if (status == success) {
				encoder.extract_chain(spec, chain);
				return success;
			}
			else {
				return status;
			}
		}

		return failure;
	}

	inline synth_result
		next_struct_solution(
			spec& spec,
			chain& chain,
			solver_wrapper& solver,
			enumerating_encoder& encoder,
			SynthMethod synth_method = SYNTH_STD)
	{
		if (!encoder.is_dirty()) {
			encoder.set_dirty(true);
			switch (synth_method) {
			case SYNTH_STD:
			case SYNTH_STD_CEGAR:
				return std_synthesize(spec, chain, solver, dynamic_cast<std_encoder&>(encoder));
			case SYNTH_FENCE:
				return fence_synthesize(spec, chain, solver, dynamic_cast<fence_encoder&>(encoder));
			default:
				fprintf(stderr, "Error: solution enumeration not supported for synth method %d\n", synth_method);
				exit(1);
			}
		}

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		// In this case, only one solution exists.
		if (spec.nr_triv == spec.get_nr_out()) {
			return failure;
		}

		if (encoder.block_solution(spec)) {
			const auto status = solver.solve(spec.conflict_limit);

			if (status == success) {
				encoder.extract_chain(spec, chain);
				return success;
			}
			else {
				return status;
			}
		}

		return failure;
	}

	inline synth_result
		maj_synthesize(
			spec& spec,
			mig& mig,
			solver_wrapper& solver,
			maj_encoder& encoder)
	{
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			mig.reset(spec.get_nr_in(), spec.get_nr_out(), 0);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				mig.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		spec.nr_steps = spec.initial_steps;
		while (true) {
			solver.restart();
			if (!encoder.encode(spec)) {
				spec.nr_steps++;
				continue;
			}

			const auto status = solver.solve(spec.conflict_limit);

			if (status == success) {
				//encoder.print_solver_state(spec);
				encoder.extract_mig(spec, mig);
				return success;
			}
			else if (status == failure) {
				spec.nr_steps++;
			}
			else {
				return timeout;
			}
		}
	}

	inline synth_result
		synthesize_3in(
			spec& spec,
			chain_3in& c,
			solver_wrapper& solver,
			encoder_3in& encoder)
	{
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			c.reset(spec.get_nr_in(), spec.get_nr_out(), 0);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				c.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		spec.nr_steps = spec.initial_steps;
		while (true) {
			solver.restart();
			if (!encoder.encode_3in(spec)) {
				spec.nr_steps++;
				continue;
			}

			const auto status = solver.solve(spec.conflict_limit);
			//const auto status = failure;
			if (status == success) {
				//encoder.print_solver_state(spec);
				encoder.extract_chain_3in(spec, c);
				return success;
			}
			else if (status == failure) {
				spec.nr_steps++;
			}
			else {
				return timeout;
			}
		}
	}

	inline synth_result
		fence_synthesize_3in(spec& spec,
			chain_3in& chain,
			solver_wrapper& solver,
			encoder_3in& encoder_dag)
	{
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			chain.reset(spec.get_nr_in(), spec.get_nr_out(), 0);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				chain.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		// As the topological synthesizer decomposes the synthesis
		// problem, to fairly count the total number of conflicts we
		// should keep track of all conflicts in existence checks.
		fence f;
		po_filter<unbounded_generator> g(
			unbounded_generator(spec.initial_steps),
			spec.get_nr_out(), 3);
		auto fence_ctr = 0;
		while (true) {
			++fence_ctr;
			g.next_fence(f);
			spec.nr_steps = f.nr_nodes();
			solver.restart();
			if (!encoder_dag.encode(spec, f)) {
				continue;
			}

			if (spec.verbosity) {
				printf("next fence (%d):\n", fence_ctr);
				print_fence(f);
				printf("\n");
				printf("nr_nodes=%d, nr_levels=%d\n", f.nr_nodes(),
					f.nr_levels());
				for (int i = 0; i < f.nr_levels(); i++) {
					printf("f[%d] = %d\n", i, f[i]);
				}
			}
			int nr_clauses = solver.nr_clauses();
			auto status = solver.solve(spec.conflict_limit);
			if (status == success) {
				encoder_dag.fence_extract_3in(spec, chain);
				//encoder.fence_print_solver_state(spec);
				return success;
			}
			else if (status == failure) {
				continue;
			}
			else {
				return timeout;
			}
		}
	}


	inline int get_init_imint(const spec& spec)
	{
		int iMint = -1;
		kitty::static_truth_table<6> tt;
		for (int i = 1; i < (1 << spec.nr_in); i++) {
			kitty::create_from_words(tt, &i, &i + 1);
			const int nOnes = kitty::count_ones(tt);
			if (nOnes < (spec.nr_in / 2) + 1) {
				continue;
			}
			iMint = i;
			break;
		}

		return iMint;
	}

	inline synth_result
		maj_cegar_synthesize(
			spec& spec,
			mig& mig,
			solver_wrapper& solver,
			maj_encoder& encoder)
	{
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			mig.reset(spec.get_nr_in(), spec.get_nr_out(), 0);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				mig.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		encoder.reset_sim_tts(spec.nr_in);
		spec.nr_steps = spec.initial_steps;
		while (true) {
			solver.restart();
			if (!encoder.cegar_encode(spec)) {
				spec.nr_steps++;
				continue;
			}
			auto iMint = get_init_imint(spec);
			//printf("initial iMint: %d\n", iMint);
			for (int i = 0; iMint != -1; i++) {
				if (!encoder.create_tt_clauses(spec, iMint - 1)) {
					spec.nr_steps++;
					break;
				}

				printf("Iter %3d : ", i);
				printf("Var =%5d  ", solver.nr_vars());
				printf("Cla =%6d  ", solver.nr_clauses());
				printf("Conf =%9d\n", solver.nr_conflicts());

				const auto status = solver.solve(spec.conflict_limit);
				if (status == success) {
					iMint = encoder.simulate(spec);
				}
				else if (status == failure) {
					spec.nr_steps++;
					break;
				}
				else {
					return timeout;
				}
			}
			if (iMint == -1) {
				encoder.extract_mig(spec, mig);
				return success;
			}
		}
	}

	inline synth_result
		maj_fence_synthesize(spec& spec, mig& mig, solver_wrapper& solver, maj_encoder& encoder)
	{
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			mig.reset(spec.get_nr_in(), spec.get_nr_out(), 0);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				mig.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		// As the topological synthesizer decomposes the synthesis
		// problem, to fairly count the total number of conflicts we
		// should keep track of all conflicts in existence checks.
		fence f;
		po_filter<unbounded_generator> g(
			unbounded_generator(spec.initial_steps),
			spec.get_nr_out(), 3);
		auto fence_ctr = 0;
		while (true) {
			++fence_ctr;
			g.next_fence(f);
			spec.nr_steps = f.nr_nodes();
			solver.restart();
			if (!encoder.encode(spec, f)) {
				continue;
			}

			if (spec.verbosity) {
				printf("next fence (%d):\n", fence_ctr);
				print_fence(f);
				printf("\n");
				printf("nr_nodes=%d, nr_levels=%d\n", f.nr_nodes(),
					f.nr_levels());
				for (int i = 0; i < f.nr_levels(); i++) {
					printf("f[%d] = %d\n", i, f[i]);
				}
			}
			auto status = solver.solve(spec.conflict_limit);
			if (status == success) {
				encoder.fence_extract_mig(spec, mig);
				//encoder.fence_print_solver_state(spec);
				return success;
			}
			else if (status == failure) {
				continue;
			}
			else {
				return timeout;
			}
		}
	}

	inline synth_result maj_fence_cegar_synthesize(
		spec& spec,
		mig& mig,
		solver_wrapper& solver,
		maj_encoder& encoder)
	{
		assert(spec.get_nr_in() >= spec.fanin);

		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			mig.reset(spec.get_nr_in(), spec.get_nr_out(), 0);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				mig.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}


		fence f;
		po_filter<unbounded_generator> g(
			unbounded_generator(spec.initial_steps),
			spec.get_nr_out(), 3);
		int fence_ctr = 0;
		while (true) {
			++fence_ctr;
			g.next_fence(f);
			spec.nr_steps = f.nr_nodes();

			if (spec.verbosity) {
				printf("  next fence (%d):\n", fence_ctr);
				print_fence(f);
				printf("\n");
				printf("nr_nodes=%d, nr_levels=%d\n", f.nr_nodes(),
					f.nr_levels());
				for (int i = 0; i < f.nr_levels(); i++) {
					printf("f[%d] = %d\n", i, f[i]);
				}
			}

			solver.restart();
			if (!encoder.cegar_encode(spec, f)) {
				continue;
			}
			while (true) {
				auto status = solver.solve(spec.conflict_limit);
				if (status == success) {
					encoder.fence_extract_mig(spec, mig);
					auto sim_tt = mig.simulate()[0];
					//auto sim_tt = encoder.simulate(spec);
					//if (spec.out_inv) {
					//    sim_tt = ~sim_tt;
					//}
					auto xor_tt = sim_tt ^ (spec[0]);
					auto first_one = kitty::find_first_one_bit(xor_tt);
					if (first_one == -1) {
						return success;
					}
					if (!encoder.fence_create_tt_clauses(spec, first_one - 1)) {
						break;
					}
				}
				else if (status == failure) {
					break;
				}
				else {
					return timeout;
				}
			}
		}
	}

	inline synth_result
		parallel_maj_synthesize(
			spec& spec,
			mig& mig,
			int num_threads = std::thread::hardware_concurrency())
	{
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			mig.reset(spec.get_nr_in(), spec.get_nr_out(), 0);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				mig.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		std::vector<std::thread> threads(num_threads);
		moodycamel::ConcurrentQueue<fence> q(num_threads * 3);

		bool finished_generating = false;
		bool* pfinished = &finished_generating;
		bool found = false;
		bool* pfound = &found;
		std::mutex found_mutex;

		spec.fanin = 3;
		spec.nr_steps = spec.initial_steps;
		while (true) {
			for (int i = 0; i < num_threads; i++) {
				threads[i] = std::thread([&spec, pfinished, pfound, &found_mutex, &mig, &q] {
					bmcg_wrapper solver;
					maj_encoder encoder(solver);
					fence local_fence;
					encoder.reset_sim_tts(spec.nr_in);

					while (!(*pfound)) {
						if (!q.try_dequeue(local_fence)) {
							if (*pfinished) {
								std::this_thread::yield();
								if (!q.try_dequeue(local_fence)) {
									break;
								}
							}
							else {
								std::this_thread::yield();
								continue;
							}
						}

						/*
						if (spec.verbosity)
						{
							std::lock_guard<std::mutex> vlock(found_mutex);
							printf("  next fence:\n");
							print_fence(local_fence);
							printf("\n");
							printf("nr_nodes=%d, nr_levels=%d\n",
								local_fence.nr_nodes(),
								local_fence.nr_levels());
						}
						*/

						synth_result status;
						solver.restart();
						if (!encoder.cegar_encode(spec, local_fence)) {
							continue;
						}
						auto iMint = get_init_imint(spec);
						for (int i = 0; !(*pfound) && iMint != -1; i++) {
							if (!encoder.fence_create_tt_clauses(spec, iMint - 1)) {
								break;
							}
							do {
								status = solver.solve(10);
								if (*pfound) {
									break;
								}
							} while (status == timeout);

							if (status == failure) {
								break;
							}
							iMint = encoder.fence_simulate(spec);
						}
						if (iMint == -1) {
							std::lock_guard<std::mutex> vlock(found_mutex);
							if (!(*pfound)) {
								encoder.fence_extract_mig(spec, mig);
								*pfound = true;
							}
						}
					}
					});
			}
			generate_fences(spec, q);
			finished_generating = true;

			for (auto& thread : threads) {
				thread.join();
			}
			if (found) {
				break;
			}
			finished_generating = false;
			spec.nr_steps++;
		}

		return success;
	}

	inline synth_result
		parallel_nocegar_maj_synthesize(
			spec& spec,
			mig& mig,
			int num_threads = std::thread::hardware_concurrency())
	{
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			mig.reset(spec.get_nr_in(), spec.get_nr_out(), 0);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				mig.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		std::vector<std::thread> threads(num_threads);
		moodycamel::ConcurrentQueue<fence> q(num_threads * 3);

		bool finished_generating = false;
		bool* pfinished = &finished_generating;
		bool found = false;
		bool* pfound = &found;
		std::mutex found_mutex;

		spec.fanin = 3;
		spec.nr_steps = spec.initial_steps;
		while (true) {
			for (int i = 0; i < num_threads; i++) {
				threads[i] = std::thread([&spec, pfinished, pfound, &found_mutex, &mig, &q] {
					bmcg_wrapper solver;
					maj_encoder encoder(solver);
					fence local_fence;

					while (!(*pfound)) {
						if (!q.try_dequeue(local_fence)) {
							if (*pfinished) {
								std::this_thread::yield();
								if (!q.try_dequeue(local_fence)) {
									break;
								}
							}
							else {
								std::this_thread::yield();
								continue;
							}
						}

						if (spec.verbosity)
						{
							std::lock_guard<std::mutex> vlock(found_mutex);
							printf("  next fence:\n");
							print_fence(local_fence);
							printf("\n");
							printf("nr_nodes=%d, nr_levels=%d\n",
								local_fence.nr_nodes(),
								local_fence.nr_levels());
						}

						synth_result status;
						solver.restart();
						if (!encoder.encode(spec, local_fence)) {
							continue;
						}
						do {
							status = solver.solve(10);
							if (*pfound) {
								break;
							}
							else if (status == success) {
								std::lock_guard<std::mutex> vlock(found_mutex);
								if (!(*pfound)) {
									encoder.fence_extract_mig(spec, mig);
									*pfound = true;
								}
							}
						} while (status == timeout);
					}
					});
			}
			generate_fences(spec, q);
			finished_generating = true;

			for (auto& thread : threads) {
				thread.join();
			}
			if (found) {
				break;
			}
			finished_generating = false;
			spec.nr_steps++;
		}

		return success;
	}

	inline synth_result
		next_solution(
			spec& spec,
			mig& mig,
			solver_wrapper& solver,
			maj_encoder& encoder)
	{
		if (!encoder.is_dirty()) {
			encoder.set_dirty(true);
			return maj_synthesize(spec, mig, solver, encoder);
		}

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		// In this case, only one solution exists.
		if (spec.nr_triv == spec.get_nr_out()) {
			return failure;
		}

		if (encoder.block_solution(spec)) {
			const auto status = solver.solve(spec.conflict_limit);

			if (status == success) {
				encoder.extract_mig(spec, mig);
				return success;
			}
			else {
				return status;
			}
		}

		return failure;
	}

	inline synth_result maj_pd_synthesize(
		spec& spec,
		mig& mig,
		const std::vector<partial_dag>& dags,
		solver_wrapper& solver,
		maj_encoder& encoder)
	{
		assert(spec.get_nr_in() >= 3);
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			mig.reset(spec.get_nr_in(), spec.get_nr_out(), 0);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				mig.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		for (auto& dag : dags) {
			spec.nr_steps = dag.nr_vertices();
			solver.restart();
			if (!encoder.encode(spec, dag)) {
				continue;
			}

			const auto status = solver.solve(0);

			if (status == success) {
				encoder.extract_mig(spec, dag, mig);
				//encoder.print_solver_state(spec, dag);
				return success;
			}
		}
		return failure;
	}

	inline synth_result maj_ser_synthesize(
		spec& spec,
		mig& mig,
		solver_wrapper& solver,
		maj_encoder& encoder,
		std::string file_prefix = "",
		int max_time = std::numeric_limits<int>::max()) // Timeout in seconds
	{
		assert(spec.get_nr_in() >= spec.fanin);
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			mig.reset(spec.get_nr_in(), spec.get_nr_out(), 0);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				mig.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		partial_dag g;
		spec.nr_steps = spec.initial_steps;
		auto begin = std::chrono::steady_clock::now();
		while (true) {
			g.reset(3, spec.nr_steps);
			const auto filename = file_prefix + "pd" + std::to_string(spec.nr_steps) + ".bin";
			auto fhandle = fopen(filename.c_str(), "rb");
			if (fhandle == NULL) {
				fprintf(stderr, "Error: unable to open file %s\n", filename.c_str());
				break;
			}

			int buf;
			while (fread(&buf, sizeof(int), 1, fhandle) != 0) {
				for (int i = 0; i < spec.nr_steps; i++) {
					auto read = fread(&buf, sizeof(int), 1, fhandle);
					assert(read > 0);
					auto fanin1 = buf;
					read = fread(&buf, sizeof(int), 1, fhandle);
					assert(read > 0);
					auto fanin2 = buf;
					read = fread(&buf, sizeof(int), 1, fhandle);
					assert(read > 0);
					auto fanin3 = buf;
					g.set_vertex(i, fanin1, fanin2, fanin3);
				}
				solver.restart();
				if (!encoder.encode(spec, g)) {
					continue;
				}
				const auto status = solver.solve(0);
				auto end = std::chrono::steady_clock::now();
				auto elapsed_time =
					std::chrono::duration_cast<std::chrono::seconds>(
						end - begin
						).count();
				if (elapsed_time > max_time) {
					return timeout;
				}
				if (status == success) {
					encoder.extract_mig(spec, g, mig);
					fclose(fhandle);
					return success;
				}
			}
			fclose(fhandle);
			spec.nr_steps++;
		}

		return failure;
	}

	inline synth_result maj_ser_synthesize_parallel(
		spec& spec,
		mig& m,
		int num_threads = std::thread::hardware_concurrency(),
		std::string file_prefix = "")
	{
		assert(spec.get_nr_in() >= spec.fanin);
		spec.preprocess();

		// The special case when the Boolean chain to be synthesized
		// consists entirely of trivial functions.
		if (spec.nr_triv == spec.get_nr_out()) {
			m.reset(spec.get_nr_in(), spec.get_nr_out(), 0);
			for (int h = 0; h < spec.get_nr_out(); h++) {
				m.set_output(h, (spec.triv_func(h) << 1) +
					((spec.out_inv >> h) & 1));
			}
			return success;
		}

		std::vector<std::thread> threads(num_threads);
		moodycamel::ConcurrentQueue<partial_dag> q(num_threads * 3);
		bool finished_generating = false;
		bool* pfinished = &finished_generating;
		int size_found = PD_SIZE_CONST;
		int* psize_found = &size_found;
		std::mutex found_mutex;

		for (int i = 0; i < num_threads; i++) {
			threads[i] = std::thread([&spec, psize_found, pfinished, &found_mutex, &m, &q] {
				percy::spec local_spec = spec;
				bsat_wrapper solver;
				maj_encoder encoder(solver);
				partial_dag dag;

				while (*psize_found > local_spec.nr_steps) {
					if (!q.try_dequeue(dag)) {
						if (*pfinished) {
							std::this_thread::yield();
							if (!q.try_dequeue(dag)) {
								break;
							}
						}
						else {
							std::this_thread::yield();
							continue;
						}
					}
					local_spec.nr_steps = dag.nr_vertices();
					synth_result status;
					solver.restart();
					if (!encoder.encode(local_spec, dag)) {
						continue;
					}
					while (true) {
						status = solver.solve(10);
						if (status == failure) {
							break;
						}
						else if (status == success) {
							std::lock_guard<std::mutex> vlock(found_mutex);
							if (*psize_found > local_spec.nr_steps) {
								encoder.extract_mig(local_spec, dag, m);
								*psize_found = local_spec.nr_steps;
							}
							break;
						}
						else if (*psize_found <= local_spec.nr_steps) {
							// Another thread found a solution that's
							// better or equal to this one.
							break;
						}
					}
				}
				});
		}

		partial_dag g;
		spec.nr_steps = spec.initial_steps;
		while (size_found == PD_SIZE_CONST) {
			g.reset(3, spec.nr_steps);
			const auto filename = file_prefix + "pd" + std::to_string(spec.nr_steps) + ".bin";
			auto fhandle = fopen(filename.c_str(), "rb");
			if (fhandle == NULL) {
				fprintf(stderr, "Error: unable to open PD file\n");
				break;
			}

			int buf;
			while (fread(&buf, sizeof(int), 1, fhandle) != 0) {
				for (int i = 0; i < spec.nr_steps; i++) {
					auto read = fread(&buf, sizeof(int), 1, fhandle);
					assert(read > 0);
					auto fanin1 = buf;
					read = fread(&buf, sizeof(int), 1, fhandle);
					assert(read > 0);
					auto fanin2 = buf;
					read = fread(&buf, sizeof(int), 1, fhandle);
					assert(read > 0);
					auto fanin3 = buf;
					g.set_vertex(i, fanin1, fanin2, fanin3);
				}
				while (!q.try_enqueue(g)) {
					if (size_found == PD_SIZE_CONST) {
						std::this_thread::yield();
					}
					else {
						break;
					}
				}
				if (size_found != PD_SIZE_CONST) {
					break;
				}
			}
			fclose(fhandle);
			spec.nr_steps++;
		}
		finished_generating = true;
		for (auto& thread : threads) {
			thread.join();
		}
		spec.nr_steps = size_found;

		return size_found == PD_SIZE_CONST ? failure : success;
	}

	
}

