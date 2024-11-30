#pragma once

#include "encoder.hpp"
#include "../fence.hpp"

namespace percy
{
	class ssv_fence2_encoder : public fence_encoder
	{
	private:
		int nr_op_vars_per_step = 3;
		int level_dist[32]; // How many steps are below a certain level
		int nr_levels; // The number of levels in the Boolean fence
		int nr_op_vars;
		int nr_out_vars;
		int nr_sim_vars;
		int nr_sel_vars;
		int nr_res_vars;
		int total_nr_vars;
		int sel_offset;
		int res_offset;
		int ops_offset;
		int out_offset;
		int sim_offset;

		int nr_op_vars2;
		int nr_out_vars2;
		int nr_sim_vars2;
		int nr_sel_vars2;
		int nr_res_vars2;
		int total_nr_vars2;
		int sel_offset2;
		int res_offset2;
		int ops_offset2;
		int out_offset2;
		int sim_offset2;

		/*std::vector<int> nr_op_vars_n;
		std::vector<int> nr_out_vars_n;
		std::vector<int> nr_sim_vars_n;
		std::vector<int> nr_sel_vars_n;
		std::vector<int> nr_res_vars_n;
		std::vector<int> total_nr_vars_n;
		std::vector<int> sel_offset_n;
		std::vector<int> res_offset_n;
		std::vector<int> ops_offset_n;
		std::vector<int> out_offset_n;
		std::vector<int> sim_offset_n;*/

		int nr_op_vars_n[2];
		int nr_out_vars_n[2];
		int nr_sim_vars_n[2];
		int nr_sel_vars_n[2];
		int nr_res_vars_n[2];
		int total_nr_vars_n[3];
		int sel_offset_n[2];
		int res_offset_n[2];
		int ops_offset_n[2];
		int out_offset_n[2];
		int sim_offset_n[2];


		pabc::Vec_Int_t* vLits; // Dynamic vector of literals

		static const int NR_SIM_TTS = 32;
		std::vector<kitty::dynamic_truth_table> sim_tts{ NR_SIM_TTS };

		bool fix_output_sim_vars(const spec& spec, int  t)
		{
			if (spec.is_dont_care(0, t + 1)) {
				return true;
			}
			auto ilast_step = spec.nr_steps - 1;
			auto outbit = kitty::get_bit(
				spec[spec.synth_func(0)], t + 1);
			if ((spec.out_inv >> spec.synth_func(0)) & 1) {
				outbit = 1 - outbit;
			}
			const auto sim_var = get_sim_var(spec, ilast_step, t);
			pabc::lit sim_lit = pabc::Abc_Var2Lit(sim_var, 1 - outbit);
			return solver->add_clause(&sim_lit, &sim_lit + 1);
		}

		bool fix_output_sim_vars_2c(const spec& spec, int  t)
		{
			if (spec.is_dont_care(0, t + 1)) {
				return true;
			}
			auto ilast_step = spec.nr_steps - 1;
			auto outbit = kitty::get_bit(
				spec[spec.synth_func(0)], t + 1);
			if ((spec.out_inv >> spec.synth_func(0)) & 1) {
				outbit = 1 - outbit;
			}
			const auto sim_var = total_nr_vars + get_sim_var(spec, ilast_step, t);
			pabc::lit sim_lit = pabc::Abc_Var2Lit(sim_var, 1 - outbit);
			return solver->add_clause(&sim_lit, &sim_lit + 1);
		}
		bool fix_output_sim_vars_nc2(const spec& spec, int  t, int ispec)
		{
			if (spec.is_dont_care(0, t + 1)) {
				return true;
			}
			auto ilast_step = spec.nr_steps - 1;
			auto outbit = kitty::get_bit(
				spec[spec.synth_func(0)], t + 1);
			if ((spec.out_inv >> spec.synth_func(0)) & 1) {
				outbit = 1 - outbit;
			}
			const auto sim_var = total_nr_vars_n[ispec] + get_sim_var_n(spec, ilast_step, t, ispec);
			pabc::lit sim_lit = pabc::Abc_Var2Lit(sim_var, 1 - outbit);
			return solver->add_clause(&sim_lit, &sim_lit + 1);
		}
		/*void vfix_output_sim_vars(const spec& spec, int  t)
		{
			auto ilast_step = spec.nr_steps - 1;

			auto outbit = kitty::get_bit(
				spec[spec.synth_func(0)], t + 1);
			if ((spec.out_inv >> spec.synth_func(0)) & 1) {
				outbit = 1 - outbit;
			}
			const auto sim_var = get_sim_var(spec, ilast_step, t);
			pabc::lit sim_lit = pabc::Abc_Var2Lit(sim_var, 1 - outbit);
			(void)solver->add_clause(&sim_lit, &sim_lit + 1);
		}*/



	public:
		const int OP_VARS_PER_STEP = 3;

		ssv_fence2_encoder(solver_wrapper& solver)
		{
			// TODO: compute better upper bound on number of literals
			vLits = pabc::Vec_IntAlloc(128);
			set_solver(solver);
		}

		~ssv_fence2_encoder()
		{
			pabc::Vec_IntFree(vLits);
		}

		int nr_svars_for_step(const spec& spec, int i) const
		{
			// Determine the level of this step.
			const auto level = get_level(spec, i + spec.nr_in);
			auto nr_svars_for_i = 0;
			assert(level > 0);
			for (auto k = first_step_on_level(level - 1);
				k < first_step_on_level(level); k++) {
				// We select k as fanin 2, so have k options 
				// (j={0,...,(k-1)}) left for fanin 1.
				nr_svars_for_i += k;
			}

			return nr_svars_for_i;
		}

		void
			update_level_map(const spec& spec, const fence& f)
		{
			nr_levels = f.nr_levels();
			level_dist[0] = spec.nr_in;
			for (int i = 1; i <= nr_levels; i++) {
				level_dist[i] = level_dist[i - 1] + f.at(i - 1);
			}
		}

		/*******************************************************************
			Returns the level (in the Boolean chain) of the specified step.
		*******************************************************************/
		int
			get_level(const spec& spec, int step_idx) const
		{
			// PIs are considered to be on level zero.
			if (step_idx < spec.nr_in) {
				return 0;
			}
			else if (step_idx == spec.nr_in) {
				// First step is always on level one
				return 1;
			}
			for (int i = 0; i <= nr_levels; i++) {
				if (level_dist[i] > step_idx) {
					return i;
				}
			}
			return -1;
		}

		/*******************************************************************
			Returns the index of the first step on the specified level.
		*******************************************************************/
		int
			first_step_on_level(int level) const
		{
			if (level == 0) { return 0; }
			return level_dist[level - 1];
		}

		int
			last_step_on_level(int level) const
		{
			return first_step_on_level(level + 1) - 1;
		}

		int
			get_op_var(const spec& spec, int step_idx, int var_idx) const
		{
			assert(step_idx < spec.nr_steps);
			assert(var_idx < OP_VARS_PER_STEP);

			return ops_offset + step_idx * OP_VARS_PER_STEP + var_idx;
		}
		int
			get_op_var_n(const spec& spec, int step_idx, int var_idx, int ispec) const
		{
			assert(step_idx < spec.nr_steps);
			assert(var_idx < OP_VARS_PER_STEP);

			return ops_offset_n[ispec] + step_idx * OP_VARS_PER_STEP + var_idx;
		}

		int get_sel_var(const spec& spec, int idx, int var_idx) const
		{
			assert(idx < spec.nr_steps);
			assert(var_idx < nr_svars_for_step(spec, idx));
			auto offset = 0;
			for (int i = 0; i < idx; i++) {
				offset += nr_svars_for_step(spec, i);
			}
			return sel_offset + offset + var_idx;
		}
		int get_sel_var_n(const spec& spec, int idx, int var_idx, int ispec) const
		{
			assert(idx < spec.nr_steps);
			assert(var_idx < nr_svars_for_step(spec, idx));
			auto offset = 0;
			for (int i = 0; i < idx; i++) {
				offset += nr_svars_for_step(spec, i);
			}
			return sel_offset_n[ispec] + offset + var_idx;
		}

		int get_out_var(const spec& spec, int h, int i) const
		{
			assert(h < spec.nr_nontriv);
			assert(i < spec.nr_steps);

			return out_offset + spec.nr_steps * h + i;
		}
		int get_out_var_n(const spec& spec, int h, int i, int ispec) const
		{
			assert(h < spec.nr_nontriv);
			assert(i < spec.nr_steps);

			return out_offset_n[ispec] + spec.nr_steps * h + i;
		}

		int get_res_var(const spec& spec, int step_idx, int res_var_idx) const
		{
			auto offset = 0;
			for (int i = 0; i < step_idx; i++) {
				offset += (nr_svars_for_step(spec, i) + 1) * (1 + 2);
			}

			return res_offset + offset + res_var_idx;
		}

		int get_sim_var(const spec& spec, int step_idx, int t) const
		{
			assert(step_idx < spec.nr_steps);
			assert(t < spec.get_tt_size());

			return sim_offset + spec.get_tt_size() * step_idx + t;
		}
		int get_sim_var_n(const spec& spec, int step_idx, int t, int ispec) const
		{
			assert(step_idx < spec.nr_steps);
			assert(t < spec.get_tt_size());

			return sim_offset_n[ispec] + spec.get_tt_size() * step_idx + t;
		}

		void create_variables(const spec& spec)
		{
			nr_op_vars = spec.nr_steps * OP_VARS_PER_STEP;
			nr_out_vars = spec.nr_nontriv * spec.nr_steps;
			nr_sim_vars = spec.nr_steps * spec.get_tt_size();

			// Ensure that steps are constrained to the proper level.
			nr_sel_vars = 0;
			for (int i = 0; i < spec.nr_steps; i++) {
				nr_sel_vars += nr_svars_for_step(spec, i);
			}

			sel_offset = 0;
			ops_offset = nr_sel_vars;
			out_offset = nr_sel_vars + nr_op_vars;
			sim_offset = nr_sel_vars + nr_op_vars + nr_out_vars;
			total_nr_vars = nr_sel_vars + nr_op_vars + nr_out_vars + nr_sim_vars;

			if (spec.verbosity) {
				printf("creating %d sel_vars\n", nr_sel_vars);
				printf("creating %d op_vars\n", nr_op_vars);
				printf("creating %d out_vars\n", nr_out_vars);
				printf("creating %d sim_vars\n", nr_sim_vars);
			}

			solver->set_nr_vars(total_nr_vars);
		}

		/*
		void create_variables_nc(const std::vector<spec> spec_all)
		{
			// for circuit 1
			nr_op_vars_n.push_back( spec_all[0].nr_steps * OP_VARS_PER_STEP); // create variables for operators
			nr_out_vars_n.push_back(spec_all[0].nr_nontriv * spec_all[0].nr_steps); // create variables for outputs position
			nr_sim_vars_n.push_back(spec_all[0].nr_steps * spec_all[0].get_tt_size()); // create variables for output truthtable of each gate

			// Ensure that steps are constrained to the proper level.
			nr_sel_vars = 0;
			for (int i = 0; i < spec_all[0].nr_steps; i++) {
				nr_sel_vars += nr_svars_for_step(spec_all[0], i);
			}
			nr_sel_vars_n.push_back(nr_sel_vars);

			sel_offset_n.push_back(0);
			ops_offset_n.push_back(nr_sel_vars_n[0]);
			out_offset_n.push_back(nr_sel_vars_n[0] + nr_op_vars_n[0]);
			sim_offset_n.push_back(nr_sel_vars_n[0] + nr_op_vars_n[0] + nr_out_vars_n[0]);
			total_nr_vars_n.push_back(0);
			total_nr_vars_n.push_back(nr_sel_vars_n[0] + nr_op_vars_n[0] + nr_out_vars_n[0] + nr_sim_vars_n[0]);

			if (spec_all[0].verbosity) {
				printf("creating %d sel_vars\n", nr_sel_vars_n[0]);
				printf("creating %d op_vars\n", nr_op_vars_n[0]);
				printf("creating %d out_vars\n", nr_out_vars_n[0]);
				printf("creating %d sim_vars\n", nr_sim_vars_n[0]);
			}

			// for circuit i>1
			for (int ispec = 1; ispec < spec_all.size(); ispec++) {
				nr_op_vars_n.push_back(spec_all[ispec].nr_steps * OP_VARS_PER_STEP);
				nr_out_vars_n.push_back(spec_all[ispec].nr_nontriv * spec_all[ispec].nr_steps);
				nr_sim_vars_n.push_back(spec_all[ispec].nr_steps * spec_all[ispec].get_tt_size());

				// Ensure that steps are constrained to the proper level.
				nr_sel_vars = 0;
				for (int i = 0; i < spec_all[ispec].nr_steps; i++) {
					nr_sel_vars += nr_svars_for_step(spec_all[ispec], i);
				}
				nr_sel_vars_n.push_back(0);

				sel_offset_n.push_back(0);
				ops_offset_n.push_back(total_nr_vars_n[ispec] + nr_sel_vars_n[ispec]);
				out_offset_n.push_back(total_nr_vars_n[ispec] + nr_sel_vars_n[ispec] + nr_op_vars_n[ispec]);
				sim_offset_n.push_back(total_nr_vars_n[ispec] + nr_sel_vars_n[ispec] + nr_op_vars_n[ispec] + nr_out_vars_n[ispec]);
				total_nr_vars_n.push_back(total_nr_vars_n[ispec] + nr_sel_vars_n[ispec] + nr_op_vars_n[ispec] + nr_sim_vars_n[ispec] + nr_out_vars_n[ispec]);

				if (spec_all[0].verbosity) {
					printf("creating %d sel_vars2\n", nr_sel_vars_n[ispec]);
					printf("creating %d op_vars2\n", nr_op_vars_n[ispec]);
					printf("creating %d out_vars2\n", nr_out_vars_n[ispec]);
					printf("creating %d sim_vars2\n", nr_sim_vars_n[ispec]);
				}
			}
			solver->set_nr_vars(total_nr_vars_n[spec_all.size()]);
		}*/

		void create_variables_nc(const std::vector<spec> spec_all)
		{
			// for circuit 1
			nr_op_vars_n[0] = (spec_all[0].nr_steps * OP_VARS_PER_STEP); // create variables for operators
			nr_out_vars_n[0] = (spec_all[0].nr_nontriv * spec_all[0].nr_steps); // create variables for outputs position
			nr_sim_vars_n[0] = (spec_all[0].nr_steps * spec_all[0].get_tt_size()); // create variables for output truthtable of each gate

			// Ensure that steps are constrained to the proper level.
			nr_sel_vars = 0;
			for (int i = 0; i < spec_all[0].nr_steps; i++) {
				nr_sel_vars += nr_svars_for_step(spec_all[0], i);
			}
			nr_sel_vars_n[0] = nr_sel_vars;

			sel_offset_n[0] = 0;
			ops_offset_n[0] = nr_sel_vars_n[0];
			out_offset_n[0] = nr_sel_vars_n[0] + nr_op_vars_n[0];
			sim_offset_n[0] = nr_sel_vars_n[0] + nr_op_vars_n[0] + nr_out_vars_n[0];
			total_nr_vars_n[0] = 0;
			total_nr_vars_n[1] = (nr_sel_vars_n[0] + nr_op_vars_n[0] + nr_out_vars_n[0] + nr_sim_vars_n[0]);

			if (spec_all[0].verbosity) {
				printf("creating %d sel_vars\n", nr_sel_vars_n[0]);
				printf("creating %d op_vars\n", nr_op_vars_n[0]);
				printf("creating %d out_vars\n", nr_out_vars_n[0]);
				printf("creating %d sim_vars\n", nr_sim_vars_n[0]);
			}

			// for circuit i>1
			for (int ispec = 1; ispec < spec_all.size(); ispec++) {
				nr_op_vars_n[ispec] = (spec_all[ispec].nr_steps * OP_VARS_PER_STEP);
				nr_out_vars_n[ispec] = (spec_all[ispec].nr_nontriv * spec_all[ispec].nr_steps);
				nr_sim_vars_n[ispec] = (spec_all[ispec].nr_steps * spec_all[ispec].get_tt_size());

				// Ensure that steps are constrained to the proper level.
				nr_sel_vars = 0;
				for (int i = 0; i < spec_all[ispec].nr_steps; i++) {
					nr_sel_vars += nr_svars_for_step(spec_all[ispec], i);
				}
				nr_sel_vars_n[ispec] = 0;
				total_nr_vars_n[ispec + 1] = 0;

				sel_offset_n[ispec] = 0;
				ops_offset_n[ispec] = (total_nr_vars_n[ispec] + nr_sel_vars_n[ispec]);
				out_offset_n[ispec] = (total_nr_vars_n[ispec] + nr_sel_vars_n[ispec] + nr_op_vars_n[ispec]);
				sim_offset_n[ispec] = (total_nr_vars_n[ispec] + nr_sel_vars_n[ispec] + nr_op_vars_n[ispec] + nr_out_vars_n[ispec]);
				total_nr_vars_n[ispec + 1] = (total_nr_vars_n[ispec] + nr_sel_vars_n[ispec] + nr_op_vars_n[ispec] + nr_sim_vars_n[ispec] + nr_out_vars_n[ispec]);

				if (spec_all[0].verbosity) {
					printf("creating %d sel_vars2\n", nr_sel_vars_n[ispec]);
					printf("creating %d op_vars2\n", nr_op_vars_n[ispec]);
					printf("creating %d out_vars2\n", nr_out_vars_n[ispec]);
					printf("creating %d sim_vars2\n", nr_sim_vars_n[ispec]);
				}
			}
			solver->set_nr_vars(total_nr_vars_n[spec_all.size()]);
		}

		void create_variables_2c(const spec& spec1, const spec& spec2)
		{
			// for circuit 1
			nr_op_vars = spec1.nr_steps * OP_VARS_PER_STEP;
			nr_out_vars = spec1.nr_nontriv * spec1.nr_steps;
			nr_sim_vars = spec1.nr_steps * spec1.get_tt_size();

			// Ensure that steps are constrained to the proper level.
			nr_sel_vars = 0;
			for (int i = 0; i < spec1.nr_steps; i++) {
				nr_sel_vars += nr_svars_for_step(spec1, i);
			}

			sel_offset = 0;
			ops_offset = nr_sel_vars;
			out_offset = nr_sel_vars + nr_op_vars;
			sim_offset = nr_sel_vars + nr_op_vars + nr_out_vars;
			total_nr_vars = nr_sel_vars + nr_op_vars + nr_out_vars + nr_sim_vars;

			if (spec1.verbosity) {
				printf("creating %d sel_vars\n", nr_sel_vars);
				printf("creating %d op_vars\n", nr_op_vars);
				printf("creating %d out_vars\n", nr_out_vars);
				printf("creating %d sim_vars\n", nr_sim_vars);
			}

			// for circuit 2
			nr_op_vars2 = spec2.nr_steps * OP_VARS_PER_STEP;
			nr_out_vars2 = spec2.nr_nontriv * spec2.nr_steps;
			nr_sim_vars2 = spec2.nr_steps * spec2.get_tt_size();

			// Ensure that steps are constrained to the proper level.
			nr_sel_vars2 = 0;
			for (int i = 0; i < spec2.nr_steps; i++) {
				nr_sel_vars2 += nr_svars_for_step(spec2, i);
			}

			sel_offset2 = 0;
			ops_offset2 = total_nr_vars + nr_sel_vars2;
			out_offset2 = total_nr_vars + nr_sel_vars2 + nr_op_vars2;
			sim_offset2 = total_nr_vars + nr_sel_vars2 + nr_op_vars2 + nr_out_vars2;
			total_nr_vars2 = total_nr_vars + nr_sel_vars2 + nr_op_vars2 + nr_sim_vars2 + nr_out_vars2;

			if (spec2.verbosity) {
				printf("creating %d sel_vars2\n", nr_sel_vars2);
				printf("creating %d op_vars2\n", nr_op_vars2);
				printf("creating %d out_vars2\n", nr_out_vars2);
				printf("creating %d sim_vars2\n", nr_sim_vars2);
			}

			solver->set_nr_vars(total_nr_vars2);
		}

		void cegar_create_variables(const spec& spec)
		{
			nr_op_vars = spec.nr_steps * OP_VARS_PER_STEP;
			nr_sim_vars = spec.nr_steps * spec.get_tt_size();

			// Ensure that steps are constrained to the proper level.
			nr_sel_vars = 0;
			nr_res_vars = 0;
			for (int i = 0; i < spec.nr_steps; i++) {
				const auto nr_svars_for_i = nr_svars_for_step(spec, i);
				nr_sel_vars += nr_svars_for_i;
				nr_res_vars += (nr_svars_for_i + 1) * (1 + 2);
			}

			sel_offset = 0;
			res_offset = nr_sel_vars;
			ops_offset = nr_sel_vars + nr_res_vars;
			sim_offset = nr_sel_vars + nr_res_vars + nr_op_vars;
			total_nr_vars = nr_sel_vars + nr_res_vars + nr_op_vars + nr_sim_vars;

			if (spec.verbosity) {
				printf("creating %d sel_vars\n", nr_sel_vars);
				printf("creating %d res_vars\n", nr_res_vars);
				printf("creating %d op_vars\n", nr_op_vars);
				printf("creating %d sim_vars\n", nr_sim_vars);
			}

			solver->set_nr_vars(total_nr_vars);
		}

		bool create_main_clauses(const spec& spec)
		{
			for (int t = 0; t < spec.get_tt_size(); t++) {
				if (!create_tt_clauses(spec, t)) {
					return false;
				}
			}
			return true;
		}
		bool create_main_clauses_1c(const spec& spec1, const spec& spec2)
		{
			for (int t = 0; t < spec1.get_tt_size(); t++) {
				if (!create_tt_clauses_1c(spec1, spec2, t)) {
					return false;
				}
			}
			return true;
		}
		bool create_main_clauses_2c(const spec& spec1, const spec& spec2)
		{
			for (int t = 0; t < spec2.get_tt_size(); t++) {
				if (!create_tt_clauses_2c(spec1, spec2, t)) {
					return false;
				}
			}
			return true;
		}

		bool create_main_clauses_1c2(const spec& spec1)
		{
			for (int t = 0; t < spec1.get_tt_size(); t++) {
				if (!create_tt_clauses_1c2(spec1, t)) {
					return false;
				}
			}
			return true;
		}
		bool create_main_clauses_2c2(const spec& spec2)
		{
			for (int t = 0; t < spec2.get_tt_size(); t++) {
				if (!create_tt_clauses_2c2(spec2, t)) {
					return false;
				}
			}
			return true;
		}
		bool create_main_clauses_nc2(const spec& spec2, const int ispec)
		{
			for (int t = 0; t < spec2.get_tt_size(); t++) {
				if (!create_tt_clauses_nc2(spec2, t, ispec)) {
					return false;
				}
			}
			return true;
		}

		bool create_output_clauses(const spec& spec)
		{
			auto status = true;

			if (spec.verbosity > 2) {
				printf("Creating output clauses (SSV-%d)\n", spec.fanin);
				printf("Nr. clauses = %d (PRE)\n", solver->nr_clauses());
			}
			// Every output points to an operand.
			if (spec.nr_nontriv > 1) {
				for (int h = 0; h < spec.nr_nontriv; h++) {
					for (int i = 0; i < spec.nr_steps; i++) {
						pabc::Vec_IntSetEntry(vLits, i,
							pabc::Abc_Var2Lit(get_out_var(spec, h, i), 0));
					}
					status &= solver->add_clause(
						pabc::Vec_IntArray(vLits),
						pabc::Vec_IntArray(vLits) + spec.nr_steps);

					if (spec.verbosity > 2) {
						printf("creating output clause: ( ");
						for (int i = 0; i < spec.nr_steps; i++) {
							printf("%sg1_%d_%d ", i > 0 ? "\\/ " : "",
								h + 1, spec.get_nr_in() + i + 1);
						}
						printf(") (status = %d)\n", status);
					}
				}
			}


			// At least one of the outputs has to refer to the final
			// operator, otherwise it may as well not be there.
			const auto last_op = spec.nr_steps - 1;
			for (int h = 0; h < spec.nr_nontriv; h++) {
				pabc::Vec_IntSetEntry(vLits, h,
					pabc::Abc_Var2Lit(get_out_var(spec, h, last_op), 0));
			}
			status &= solver->add_clause(
				pabc::Vec_IntArray(vLits),
				pabc::Vec_IntArray(vLits) + spec.nr_nontriv);

			if (spec.verbosity > 2) {
				printf("creating output clause: ( ");
				for (int h = 0; h < spec.nr_nontriv; h++) {
					printf("%sg_%d_%d ", h > 0 ? "\\/ " : "",
						h + 1, spec.get_nr_in() + last_op + 1);
				}
				printf(") (status = %d)\n", status);
				printf("Nr. clauses = %d (POST)\n", solver->nr_clauses());
			}

			return status;
		}

		bool create_output_clauses_2c(const spec& spec)
		{
			auto status = true;

			if (spec.verbosity > 2) {
				printf("Creating output clauses (SSV-%d)\n", spec.fanin);
				printf("Nr. clauses = %d (PRE)\n", solver->nr_clauses());
			}
			// Every output points to an operand.
			if (spec.nr_nontriv > 1) {
				for (int h = 0; h < spec.nr_nontriv; h++) {
					for (int i = 0; i < spec.nr_steps; i++) {
						pabc::Vec_IntSetEntry(vLits, i,
							pabc::Abc_Var2Lit(total_nr_vars + get_out_var(spec, h, i), 0));
					}
					status &= solver->add_clause(
						pabc::Vec_IntArray(vLits),
						pabc::Vec_IntArray(vLits) + spec.nr_steps);

					if (spec.verbosity > 2) {
						printf("creating output clause: ( ");
						for (int i = 0; i < spec.nr_steps; i++) {
							printf("%sg2_%d_%d ", i > 0 ? "\\/ " : "",
								h + 1, spec.get_nr_in() + i + 1);
						}
						printf(") (status = %d)\n", status);
					}
				}
			}


			// At least one of the outputs has to refer to the final
			// operator, otherwise it may as well not be there.
			const auto last_op = spec.nr_steps - 1;
			for (int h = 0; h < spec.nr_nontriv; h++) {
				pabc::Vec_IntSetEntry(vLits, h,
					pabc::Abc_Var2Lit(total_nr_vars + get_out_var(spec, h, last_op), 0));
			}
			status &= solver->add_clause(
				pabc::Vec_IntArray(vLits),
				pabc::Vec_IntArray(vLits) + spec.nr_nontriv);

			if (spec.verbosity > 2) {
				printf("creating output clause: ( ");
				for (int h = 0; h < spec.nr_nontriv; h++) {
					printf("%sg_%d_%d ", h > 0 ? "\\/ " : "",
						h + 1, spec.get_nr_in() + last_op + 1);
				}
				printf(") (status = %d)\n", status);
				printf("Nr. clauses = %d (POST)\n", solver->nr_clauses());
			}

			return status;
		}

		bool create_removerez_clauses_nc(const std::vector<spec> spec_all, std::vector<int>& c)
		{
			int pLits[10000];
			int ctr = 0;
			auto status = true;
			int var_temp;
			/*for (int i = 0; i < total_nr_vars_n[2]; i++)
			{
				if ((sel_offset_n[0] <= i) & (i < nr_sel_vars_n[0]))
				{
					if (c[i] == 0)
					{
						var_temp = pabc::Abc_Var2Lit(i, 0);
						pLits[ctr++] = var_temp;
					}
					else
					{
						var_temp = pabc::Abc_Var2Lit(i, 1);
						pLits[ctr++] = var_temp;
					}
				}
			}*/
			//for (int i = 0; i < total_nr_vars_n[2]; i++)
			for (int i = 0; i < total_nr_vars_n[2]; i++)
			//for (int i = 0; i < c.size(); i++)
			{
				//if ((sel_offset_n[0] <= i) & (i < out_offset_n[0]))
				//if (((sel_offset_n[0] <= i) & (i < nr_out_vars_n[0])) || ((out_offset_n[0] <= i) & (i < nr_sim_vars_n[0]))  )
				{
					if (c[i] == 0)
					{
						var_temp = pabc::Abc_Var2Lit(i, 0);
						pLits[ctr++] = var_temp;
					}
					else
					{
						var_temp = pabc::Abc_Var2Lit(i, 1);
						pLits[ctr++] = var_temp;
					}
				}
				
				/*if ((out_offset_n[0] <= i) & (i < sim_offset_n[0]))
					//if (((sel_offset_n[0] <= i) & (i < nr_out_vars_n[0])) || ((out_offset_n[0] <= i) & (i < nr_sim_vars_n[0]))  )
				{
					if (c[i] == 0)
					{
						var_temp = pabc::Abc_Var2Lit(i, 0);
						pLits[ctr++] = var_temp;
					}
					else
					{
						var_temp = pabc::Abc_Var2Lit(i, 1);
						pLits[ctr++] = var_temp;
					}
				}*/


			}
			status &= solver->add_clause(pLits, pLits + ctr);
			return status;
			/*for (int ispec = 0; ispec < spec_all.size(); ispec++) {
				kitty::dynamic_truth_table op(2);
				for (int i = 0; i < spec.nr_steps; i++) {
					for (int j = 0; j < OP_VARS_PER_STEP; j++) {
						if (solver->var_value(total_nr_vars_n[ispec] + get_op_var_n(spec, i, j, ispec)))
							kitty::set_bit(op, j + 1);
						else
							kitty::clear_bit(op, j + 1);
					}

					auto ctr = 0;
					const auto level = get_level(spec, spec.nr_in + i);
					for (int k = first_step_on_level(level - 1);
						k < first_step_on_level(level); k++) {
						for (int j = 0; j < k; j++) {
							const auto sel_var = get_sel_var_n(spec, i, ctr++, ispec);
							if (solver->var_value(sel_var)) {
								if (spec.verbosity) {
									printf("  with operands ");
									printf("x_%d ", j + 1);
									printf("x_%d ", k + 1);
								}
								chain.set_step(i, j, k, op);
								break;
							}
						}
					}

					if (spec.verbosity) {
						printf("\n");
					}
				}

				// TODO: support multiple outputs
				auto triv_count = 0, nontriv_count = 0;
				for (int h = 0; h < spec.get_nr_out(); h++) {
					if ((spec.triv_flag >> h) & 1) {
						chain.set_output(h,
							(spec.triv_func(triv_count++) << 1) +
							((spec.out_inv >> h) & 1));
						continue;
					}
					for (int i = 0; i < spec.nr_steps; i++) {
						if (solver->var_value(total_nr_vars_n[ispec] + get_out_var_n(spec, nontriv_count, i, ispec))) {
							chain.set_output(h,
								((i + spec.get_nr_in() + 1) << 1) +
								((spec.out_inv >> h) & 1));
							nontriv_count++;
							break;
						}
					}
				}
			}*/
		}
		bool create_output_clauses_nc(const std::vector<spec> spec_all)
		{
			auto status = true;
			for (int ispec = 0; ispec < spec_all.size(); ispec++) {
				if (spec_all[ispec].verbosity > 2) {
					printf("Creating output clauses (SSV-%d)\n", spec_all[ispec].fanin);
					printf("Nr. clauses = %d (PRE)\n", solver->nr_clauses());
				}
				// Every output points to an operand.
				if (spec_all[ispec].nr_nontriv > 0) {
					for (int h = 0; h < spec_all[ispec].nr_nontriv; h++) {
						for (int i = 0; i < spec_all[ispec].nr_steps; i++) {
							pabc::Vec_IntSetEntry(vLits, i,
								pabc::Abc_Var2Lit(get_out_var_n(spec_all[ispec], h, i, ispec), 0));
						}
						status &= solver->add_clause(
							pabc::Vec_IntArray(vLits),
							pabc::Vec_IntArray(vLits) + spec_all[ispec].nr_steps);

						if (spec_all[0].verbosity > 2) {
							printf("creating output clause: ( ");
							for (int i = 0; i < spec_all[i].nr_steps; i++) {
								printf("%sg2_%d_%d ", i > 0 ? "\\/ " : "",
									h + 1, spec_all[i].get_nr_in() + i + 1);
							}
							printf(") (status = %d)\n", status);
						}
					}
				}


				// At least one of the outputs has to refer to the final
				// operator, otherwise it may as well not be there.
				const auto last_op = spec_all[ispec].nr_steps - 1;
				for (int h = 0; h < spec_all[ispec].nr_nontriv; h++) {
					pabc::Vec_IntSetEntry(vLits, h,
						pabc::Abc_Var2Lit(get_out_var_n(spec_all[ispec], h, last_op, ispec), 0));
				}
				status &= solver->add_clause(
					pabc::Vec_IntArray(vLits),
					pabc::Vec_IntArray(vLits) + spec_all[ispec].nr_nontriv);

				if (spec_all[0].verbosity > 2) {
					printf("creating output clause: ( ");
					for (int h = 0; h < spec_all[ispec].nr_nontriv; h++) {
						printf("%sg_%d_%d ", h > 0 ? "\\/ " : "",
							h + 1, spec_all[ispec].get_nr_in() + last_op + 1);
					}
					printf(") (status = %d)\n", status);
					printf("Nr. clauses = %d (POST)\n", solver->nr_clauses());
				}
			}
			return status;
		}

		bool create_sameout_clauses(const spec& spec1, const spec& spec2)
		{
			auto status = true;
			assert(spec1.get_nr_out() <= spec2.get_nr_out());
			for (int h = 0; h < spec1.nr_nontriv; h++) {
				for (int i = 0; i < spec1.nr_steps; i++) {
					for (int j = 0; j < spec1.nr_steps; j++) {
						if (i == j) {
							continue;
						}
						else {
							int pLits[2];
							pLits[0] = pabc::Abc_Var2Lit(get_out_var(spec1, h, i), 1);
							pLits[1] = pabc::Abc_Var2Lit(total_nr_vars + get_out_var(spec2, h, j), 1);
							status &= solver->add_clause(pLits, pLits + 2);
							if (spec1.verbosity > 2) {
								printf("creating output seq clause: ( ");
								printf("!g1_%d_%d%s",
									h + 1, spec1.get_nr_in() + i + 1, " \\/ ");
								printf("!g2_%d_%d ",
									h + 1, spec1.get_nr_in() + j + 1);
								printf(") (status = %d)\n", status);
							}
						}
					}
				}
			}
			return status;
		}

		bool create_sameout_clauses_nc(const std::vector<spec> spec_all)
		{
			auto status = true;
			for (int ispec = 1; ispec < spec_all.size(); ispec++) {
				assert(spec_all[ispec - 1].get_nr_out() <= spec_all[ispec].get_nr_out());
				for (int h = 0; h < spec_all[ispec - 1].nr_nontriv; h++) {
					for (int i = 0; i < spec_all[ispec - 1].nr_steps; i++) {
						for (int j = 0; j < spec_all[ispec - 1].nr_steps; j++) {
							if (i == j) {
								continue;
							}
							else {
								int pLits[2];
								pLits[0] = pabc::Abc_Var2Lit(get_out_var_n(spec_all[ispec - 1], h, i, ispec), 1);
								pLits[1] = pabc::Abc_Var2Lit(total_nr_vars_n[ispec] + get_out_var_n(spec_all[ispec], h, j, ispec), 1);
								status &= solver->add_clause(pLits, pLits + 2);
								if (spec_all[ispec - 1].verbosity > 2) {
									printf("creating output seq clause: ( ");
									printf("!g1_%d_%d%s",
										h + 1, spec_all[ispec - 1].get_nr_in() + i + 1, " \\/ ");
									printf("!g2_%d_%d ",
										h + 1, spec_all[ispec - 1].get_nr_in() + j + 1);
									printf(") (status = %d)\n", status);
								}
							}
						}
					}
				}
			}
			return status;
		}

		/*******************************************************************
			Add clauses that prevent trivial variable projection and
			constant operators from being synthesized.
		*******************************************************************/

		bool create_nontriv_clauses(const spec& spec)
		{
			int pLits[3];
			bool status = true;
			for (int i = 0; i < spec.nr_steps; i++) {
				// Dissallow the constant zero operator.
				pLits[0] = pabc::Abc_Var2Lit(get_op_var(spec, i, 0), 0);
				pLits[1] = pabc::Abc_Var2Lit(get_op_var(spec, i, 1), 0);
				pLits[2] = pabc::Abc_Var2Lit(get_op_var(spec, i, 2), 0);
				status &= solver->add_clause(pLits, pLits + 3);

				// Dissallow variable projections.
				pLits[0] = pabc::Abc_Var2Lit(get_op_var(spec, i, 0), 0);
				pLits[1] = pabc::Abc_Var2Lit(get_op_var(spec, i, 1), 1);
				pLits[2] = pabc::Abc_Var2Lit(get_op_var(spec, i, 2), 1);
				status &= solver->add_clause(pLits, pLits + 3);

				pLits[0] = pabc::Abc_Var2Lit(get_op_var(spec, i, 0), 1);
				pLits[1] = pabc::Abc_Var2Lit(get_op_var(spec, i, 1), 0);
				pLits[2] = pabc::Abc_Var2Lit(get_op_var(spec, i, 2), 1);
				status &= solver->add_clause(pLits, pLits + 3);
			}

			return status;
		}
		bool create_nontriv_clauses_2c(const spec& spec)
		{
			int pLits[3];
			bool status = true;
			for (int i = 0; i < spec.nr_steps; i++) {
				// Dissallow the constant zero operator.
				pLits[0] = pabc::Abc_Var2Lit(total_nr_vars + get_op_var(spec, i, 0), 0);
				pLits[1] = pabc::Abc_Var2Lit(total_nr_vars + get_op_var(spec, i, 1), 0);
				pLits[2] = pabc::Abc_Var2Lit(total_nr_vars + get_op_var(spec, i, 2), 0);
				status &= solver->add_clause(pLits, pLits + 3);

				// Dissallow variable projections.
				pLits[0] = pabc::Abc_Var2Lit(total_nr_vars + get_op_var(spec, i, 0), 0);
				pLits[1] = pabc::Abc_Var2Lit(total_nr_vars + get_op_var(spec, i, 1), 1);
				pLits[2] = pabc::Abc_Var2Lit(total_nr_vars + get_op_var(spec, i, 2), 1);
				status &= solver->add_clause(pLits, pLits + 3);

				pLits[0] = pabc::Abc_Var2Lit(total_nr_vars + get_op_var(spec, i, 0), 1);
				pLits[1] = pabc::Abc_Var2Lit(total_nr_vars + get_op_var(spec, i, 1), 0);
				pLits[2] = pabc::Abc_Var2Lit(total_nr_vars + get_op_var(spec, i, 2), 1);
				status &= solver->add_clause(pLits, pLits + 3);
			}

			return status;
		}
		bool create_nontriv_clauses_nc(const spec& spec)
		{
			int pLits[3];
			bool status = true;
			for (int i = 0; i < spec.nr_steps; i++) {
				// Dissallow the constant zero operator.
				pLits[0] = pabc::Abc_Var2Lit(get_op_var_n(spec, i, 0, 0), 0);
				pLits[1] = pabc::Abc_Var2Lit(get_op_var_n(spec, i, 1, 0), 0);
				pLits[2] = pabc::Abc_Var2Lit(get_op_var_n(spec, i, 2, 0), 0);
				status &= solver->add_clause(pLits, pLits + 3);

				// Dissallow variable projections.
				pLits[0] = pabc::Abc_Var2Lit(get_op_var_n(spec, i, 0, 0), 0);
				pLits[1] = pabc::Abc_Var2Lit(get_op_var_n(spec, i, 1, 0), 1);
				pLits[2] = pabc::Abc_Var2Lit(get_op_var_n(spec, i, 2, 0), 1);
				status &= solver->add_clause(pLits, pLits + 3);

				pLits[0] = pabc::Abc_Var2Lit(get_op_var_n(spec, i, 0, 0), 1);
				pLits[1] = pabc::Abc_Var2Lit(get_op_var_n(spec, i, 1, 0), 0);
				pLits[2] = pabc::Abc_Var2Lit(get_op_var_n(spec, i, 2, 0), 1);
				status &= solver->add_clause(pLits, pLits + 3);
			}
			return status;
		}
		bool create_nontriv_clauses_nc2(const spec& spec)
		{
			int pLits[3];
			bool status = true;
			for (int i = 0; i < spec.nr_steps; i++) {
				// Dissallow the constant zero operator.
				pLits[0] = pabc::Abc_Var2Lit(get_op_var_n(spec, i, 0, 0), 0);
				pLits[1] = pabc::Abc_Var2Lit(get_op_var_n(spec, i, 1, 0), 0);
				pLits[2] = pabc::Abc_Var2Lit(get_op_var_n(spec, i, 2, 0), 0);
				status &= solver->add_clause(pLits, pLits + 3);
				/*
				// Dissallow variable projections.
				pLits[0] = pabc::Abc_Var2Lit(total_nr_vars_n[0] + get_op_var_n(spec, i, 0, 0), 0);
				pLits[1] = pabc::Abc_Var2Lit(total_nr_vars_n[0] + get_op_var_n(spec, i, 1, 0), 1);
				pLits[2] = pabc::Abc_Var2Lit(total_nr_vars_n[0] + get_op_var_n(spec, i, 2, 0), 1);
				status &= solver->add_clause(pLits, pLits + 3);

				pLits[0] = pabc::Abc_Var2Lit(total_nr_vars_n[0] + get_op_var_n(spec, i, 0, 0), 1);
				pLits[1] = pabc::Abc_Var2Lit(total_nr_vars_n[0] + get_op_var_n(spec, i, 1, 0), 0);
				pLits[2] = pabc::Abc_Var2Lit(total_nr_vars_n[0] + get_op_var_n(spec, i, 2, 0), 1);
				status &= solver->add_clause(pLits, pLits + 3); */
			}
			for (int i = 0; i < spec.nr_steps; i++) {
				// Dissallow the constant zero operator.
				pLits[0] = pabc::Abc_Var2Lit(get_op_var_n(spec, i, 0, 0), 0);
				pLits[1] = pabc::Abc_Var2Lit(get_op_var_n(spec, i, 1, 0), 0);
				pLits[2] = pabc::Abc_Var2Lit(get_op_var_n(spec, i, 2, 0), 0);
				status &= solver->add_clause(pLits, pLits + 3);
				/*
				// Dissallow variable projections.
				pLits[0] = pabc::Abc_Var2Lit(total_nr_vars_n[1] + get_op_var_n(spec, i, 0, 0), 0);
				pLits[1] = pabc::Abc_Var2Lit(total_nr_vars_n[1] + get_op_var_n(spec, i, 1, 0), 1);
				pLits[2] = pabc::Abc_Var2Lit(total_nr_vars_n[1] + get_op_var_n(spec, i, 2, 0), 1);
				status &= solver->add_clause(pLits, pLits + 3);

				pLits[0] = pabc::Abc_Var2Lit(total_nr_vars_n[1] + get_op_var_n(spec, i, 0, 0), 1);
				pLits[1] = pabc::Abc_Var2Lit(total_nr_vars_n[1] + get_op_var_n(spec, i, 1, 0), 0);
				pLits[2] = pabc::Abc_Var2Lit(total_nr_vars_n[1] + get_op_var_n(spec, i, 2, 0), 1);
				status &= solver->add_clause(pLits, pLits + 3);
				*/
			}
			return status;
		}

		bool create_tt_clauses(const spec& spec, int t) override
		{
			auto ret = true;
			int pLits[2];
			for (int i = 0; i < spec.nr_steps; i++) {
				auto level = get_level(spec, i + spec.nr_in);
				assert(level > 0);
				auto ctr = 0;
				for (int k = first_step_on_level(level - 1);
					k < first_step_on_level(level); k++) {
					for (int j = 0; j < k; j++) {
						const auto sel_var = get_sel_var(spec, i, ctr++);
						ret &= add_simulation_clause(spec, t, i, j, k, 0, 0, 1, sel_var);
						ret &= add_simulation_clause(spec, t, i, j, k, 0, 1, 0, sel_var);
						ret &= add_simulation_clause(spec, t, i, j, k, 0, 1, 1, sel_var);
						ret &= add_simulation_clause(spec, t, i, j, k, 1, 0, 0, sel_var);
						ret &= add_simulation_clause(spec, t, i, j, k, 1, 0, 1, sel_var);
						ret &= add_simulation_clause(spec, t, i, j, k, 1, 1, 0, sel_var);
						ret &= add_simulation_clause(spec, t, i, j, k, 1, 1, 1, sel_var);
					}
				}
				if (spec.verbosity > 2) {
					printf("Nr. clauses = %d (POST)\n", solver->nr_clauses());
				}
				// If an output has selected this particular operand, we
						// need to ensure that this operand's truth table satisfies
						// the specified output function.
				for (int h = 0; h < spec.nr_nontriv; h++) {
					if (spec.is_dont_care(h, t + 1)) {
						continue;
					}
					auto outbit = kitty::get_bit(
						spec[spec.synth_func(h)], t + 1);
					if ((spec.out_inv >> spec.synth_func(h)) & 1) {
						outbit = 1 - outbit;
					}
					pLits[0] = pabc::Abc_Var2Lit(get_out_var(spec, h, i), 1);
					pLits[1] = pabc::Abc_Var2Lit(get_sim_var(spec, i, t),
						1 - outbit);
					ret &= solver->add_clause(pLits, pLits + 2);
					if (spec.verbosity > 2) {
						printf("creating oimp clause: ( ");
						if (spec.verbosity > 2) {
							printf("Add clauses = %d \\/ %d (POST)\n", pLits[0], pLits[1]);
						}
						/*printf("!g_%d_%d \\/ %sx_%d_%d ) (status=%d)\n",
							h + 1, // nontrive output number
							spec.get_nr_in() + i + 1, // step number
							(1 - outbit) ? "!" : "",
							spec.get_nr_in() + i + 1, // step number
							t + 2, // position in tt
							ret);*/
					}
				}
			}
			//ret &= fix_output_sim_vars(spec, t);

			return ret;
		}
		bool create_tt_clauses_1c(const spec& spec1, const spec& spec2, int t)
		{
			auto ret = true;
			int pLits[4];
			for (int i = 0; i < spec1.nr_steps; i++) {
				auto level = get_level(spec1, i + spec1.nr_in);
				assert(level > 0);
				auto ctr = 0;
				for (int k = first_step_on_level(level - 1);
					k < first_step_on_level(level); k++) {
					for (int j = 0; j < k; j++) {
						const auto sel_var = get_sel_var(spec1, i, ctr++);
						ret &= add_simulation_clause(spec1, t, i, j, k, 0, 0, 1, sel_var);
						ret &= add_simulation_clause(spec1, t, i, j, k, 0, 1, 0, sel_var);
						ret &= add_simulation_clause(spec1, t, i, j, k, 0, 1, 1, sel_var);
						ret &= add_simulation_clause(spec1, t, i, j, k, 1, 0, 0, sel_var);
						ret &= add_simulation_clause(spec1, t, i, j, k, 1, 0, 1, sel_var);
						ret &= add_simulation_clause(spec1, t, i, j, k, 1, 1, 0, sel_var);
						ret &= add_simulation_clause(spec1, t, i, j, k, 1, 1, 1, sel_var);
					}
				}
				if (spec1.verbosity > 2) {
					printf("Nr. clauses = %d (POST)\n", solver->nr_clauses());
				}
				// If an output has selected this particular operand, we
						// need to ensure that this operand's truth table satisfies
						// the specified output function.
				for (int h = 0; h < spec1.nr_nontriv; h++) {
					if (spec1.is_dont_care(h, t + 1)) {
						continue;
					}
					if (spec2.is_dont_care(h, t + 1)) {
						continue;
					}
					auto outbit1 = kitty::get_bit(
						spec1[spec1.synth_func(h)], t + 1);
					if ((spec1.out_inv >> spec1.synth_func(h)) & 1) {
						outbit1 = 1 - outbit1;
					}
					pLits[0] = pabc::Abc_Var2Lit(get_out_var(spec1, h, i), 1);
					pLits[1] = pabc::Abc_Var2Lit(get_sim_var(spec1, i, t),
						1 - outbit1);
					//////////////////////////////////////////
					auto outbit2 = kitty::get_bit(
						spec2[spec2.synth_func(h)], t + 1);
					if ((spec2.out_inv >> spec2.synth_func(h)) & 1) {
						outbit2 = 1 - outbit2;
					}
					pLits[2] = pabc::Abc_Var2Lit(total_nr_vars + get_out_var(spec1, h, i), 1);
					pLits[3] = pabc::Abc_Var2Lit(total_nr_vars + get_sim_var(spec1, i, t),
						1 - outbit2);
					ret &= solver->add_clause(pLits, pLits + 4);
					if (spec1.verbosity > 2) {
						printf("creating oimp clause: ( ");
						//if (spec1.verbosity > 2) {
							//printf("Add clauses = %d \\/ %d \\/ %d \\/ %d(POST)\n", pLits[0], pLits[1], pLits[2], pLits[3]);
						//}
						printf("!g1_%d_%d \\/ %sx1_%d_%d \\/ !g2_%d_%d \\/ %sx2_%d_%d ) (status=%d)\n",
							h + 1, // nontrive output number
							spec1.get_nr_in() + i + 1, // step number
							(1 - outbit1) ? "!" : "",
							spec1.get_nr_in() + i + 1, // step number
							t + 2, // position in tt
							h + 1, // nontrive output number
							spec1.get_nr_in() + i + 1, // step number
							(1 - outbit2) ? "!" : "",
							spec1.get_nr_in() + i + 1, // step number
							t + 2, // position in tt
							ret);
					}
				}
			}
			//ret &= fix_output_sim_vars(spec, t);

			return ret;
		}
		bool create_tt_clauses_2c(const spec& spec1, const spec& spec2, int t)
		{
			auto ret = true;
			int pLits[2];
			for (int i = 0; i < spec2.nr_steps; i++) {
				auto level = get_level(spec2, i + spec2.nr_in);
				assert(level > 0);
				auto ctr = 0;
				for (int k = first_step_on_level(level - 1);
					k < first_step_on_level(level); k++) {
					for (int j = 0; j < k; j++) {
						const auto sel_var = get_sel_var(spec2, i, ctr++);
						ret &= add_simulation_clause_2c(spec2, t, i, j, k, 0, 0, 1, sel_var);
						ret &= add_simulation_clause_2c(spec2, t, i, j, k, 0, 1, 0, sel_var);
						ret &= add_simulation_clause_2c(spec2, t, i, j, k, 0, 1, 1, sel_var);
						ret &= add_simulation_clause_2c(spec2, t, i, j, k, 1, 0, 0, sel_var);
						ret &= add_simulation_clause_2c(spec2, t, i, j, k, 1, 0, 1, sel_var);
						ret &= add_simulation_clause_2c(spec2, t, i, j, k, 1, 1, 0, sel_var);
						ret &= add_simulation_clause_2c(spec2, t, i, j, k, 1, 1, 1, sel_var);
					}
				}
			}
			assert(spec1.nr_steps <= spec2.nr_steps);
			if (spec1.nr_steps < spec2.nr_steps) {
				for (int i = spec1.nr_steps - 1; i < spec2.nr_steps; i++) {
					// If an output has selected this particular operand, we
							// need to ensure that this operand's truth table satisfies
							// the specified output function.
					for (int h = 0; h < spec2.nr_nontriv; h++) {
						if (spec2.is_dont_care(h, t + 1)) {
							continue;
						}
						auto outbit = kitty::get_bit(
							spec2[spec2.synth_func(h)], t + 1);
						if ((spec2.out_inv >> spec2.synth_func(h)) & 1) {
							outbit = 1 - outbit;
						}
						pLits[0] = pabc::Abc_Var2Lit(total_nr_vars + get_out_var(spec2, h, i), 1);
						pLits[1] = pabc::Abc_Var2Lit(total_nr_vars + get_sim_var(spec2, i, t),
							1 - outbit);
						ret &= solver->add_clause(pLits, pLits + 2);
						if (spec2.verbosity > 2) {
							printf("creating oimp clause: ( ");
							printf("!g2_%d_%d \\/ %sx2_%d_%d ) (status=%d)\n",
								h + 1, // nontrive output number
								spec2.get_nr_in() + i + 1, // step number
								(1 - outbit) ? "!" : "",
								spec2.get_nr_in() + i + 1, // step number
								t + 2, // position in tt
								ret);
						}
					}
				}
			}
			//ret &= fix_output_sim_vars_2c(spec, t);

			return ret;
		}

		bool create_tt_clauses_1c2(const spec& spec1, int t)
		{
			auto ret = true;
			int pLits[2];
			for (int i = 0; i < spec1.nr_steps; i++) {
				auto level = get_level(spec1, i + spec1.nr_in);
				assert(level > 0);
				auto ctr = 0;
				for (int k = first_step_on_level(level - 1);
					k < first_step_on_level(level); k++) {
					for (int j = 0; j < k; j++) {
						const auto sel_var = get_sel_var(spec1, i, ctr++);
						ret &= add_simulation_clause(spec1, t, i, j, k, 0, 0, 1, sel_var);
						ret &= add_simulation_clause(spec1, t, i, j, k, 0, 1, 0, sel_var);
						ret &= add_simulation_clause(spec1, t, i, j, k, 0, 1, 1, sel_var);
						ret &= add_simulation_clause(spec1, t, i, j, k, 1, 0, 0, sel_var);
						ret &= add_simulation_clause(spec1, t, i, j, k, 1, 0, 1, sel_var);
						ret &= add_simulation_clause(spec1, t, i, j, k, 1, 1, 0, sel_var);
						ret &= add_simulation_clause(spec1, t, i, j, k, 1, 1, 1, sel_var);
					}
				}
				if (spec1.verbosity > 2) {
					printf("Nr. clauses = %d (POST)\n", solver->nr_clauses());
				}
				// If an output has selected this particular operand, we
						// need to ensure that this operand's truth table satisfies
						// the specified output function.
				for (int h = 0; h < spec1.nr_nontriv; h++) {
					if (spec1.is_dont_care(h, t + 1)) {
						continue;
					}
					auto outbit1 = kitty::get_bit(
						spec1[spec1.synth_func(h)], t + 1);
					if ((spec1.out_inv >> spec1.synth_func(h)) & 1) {
						outbit1 = 1 - outbit1;
					}
					pLits[0] = pabc::Abc_Var2Lit(get_out_var(spec1, h, i), 1);
					pLits[1] = pabc::Abc_Var2Lit(get_sim_var(spec1, i, t),
						1 - outbit1);
					ret &= solver->add_clause(pLits, pLits + 2);
					if (spec1.verbosity > 2) {
						printf("creating oimp clause: ( ");
						//if (spec1.verbosity > 2) {
							//printf("Add clauses = %d \\/ %d \\/ %d \\/ %d(POST)\n", pLits[0], pLits[1], pLits[2], pLits[3]);
						//}
						printf("!g1_%d_%d \\/ %sx1_%d_%d ) (status=%d)\n",
							h + 1, // nontrive output number
							spec1.get_nr_in() + i + 1, // step number
							(1 - outbit1) ? "!" : "",
							spec1.get_nr_in() + i + 1, // step number
							t + 2, // position in tt
							ret);
					}
				}
			}
			//ret &= fix_output_sim_vars(spec, t);

			return ret;
		}
		bool create_tt_clauses_2c2(const spec& spec2, int t)
		{
			auto ret = true;
			int pLits[2];
			for (int i = 0; i < spec2.nr_steps; i++) {
				auto level = get_level(spec2, i + spec2.nr_in);
				assert(level > 0);
				auto ctr = 0;
				for (int k = first_step_on_level(level - 1);
					k < first_step_on_level(level); k++) {
					for (int j = 0; j < k; j++) {
						const auto sel_var = get_sel_var(spec2, i, ctr++);
						ret &= add_simulation_clause_2c(spec2, t, i, j, k, 0, 0, 1, sel_var);
						ret &= add_simulation_clause_2c(spec2, t, i, j, k, 0, 1, 0, sel_var);
						ret &= add_simulation_clause_2c(spec2, t, i, j, k, 0, 1, 1, sel_var);
						ret &= add_simulation_clause_2c(spec2, t, i, j, k, 1, 0, 0, sel_var);
						ret &= add_simulation_clause_2c(spec2, t, i, j, k, 1, 0, 1, sel_var);
						ret &= add_simulation_clause_2c(spec2, t, i, j, k, 1, 1, 0, sel_var);
						ret &= add_simulation_clause_2c(spec2, t, i, j, k, 1, 1, 1, sel_var);
					}
				}
			}
			//assert(spec1.nr_steps <= spec1.nr_steps);
			//if (spec1.nr_steps < spec1.nr_steps) {
			for (int i = 0; i < spec2.nr_steps; i++) {
				// If an output has selected this particular operand, we
						// need to ensure that this operand's truth table satisfies
						// the specified output function.
				for (int h = 0; h < spec2.nr_nontriv; h++) {
					if (spec2.is_dont_care(h, t + 1)) {
						continue;
					}
					auto outbit = kitty::get_bit(
						spec2[spec2.synth_func(h)], t + 1);
					if ((spec2.out_inv >> spec2.synth_func(h)) & 1) {
						outbit = 1 - outbit;
					}
					pLits[0] = pabc::Abc_Var2Lit(total_nr_vars + get_out_var(spec2, h, i), 1);
					pLits[1] = pabc::Abc_Var2Lit(total_nr_vars + get_sim_var(spec2, i, t),
						1 - outbit);
					ret &= solver->add_clause(pLits, pLits + 2);
					if (spec2.verbosity > 2) {
						printf("creating oimp clause: ( ");
						printf("!g2_%d_%d \\/ %sx2_%d_%d ) (status=%d)\n",
							h + 1, // nontrive output number
							spec2.get_nr_in() + i + 1, // step number
							(1 - outbit) ? "!" : "",
							spec2.get_nr_in() + i + 1, // step number
							t + 2, // position in tt
							ret);
					}
				}
			}
			//}
			//ret &= fix_output_sim_vars_2c(spec, t);

			return ret;
		}

		bool create_tt_clauses_nc2(const spec& spec2, int t, int ispec)
		{
			auto ret = true;
			int pLits[2];
			for (int i = 0; i < spec2.nr_steps; i++) { // traverse all the steps
				auto level = get_level(spec2, i + spec2.nr_in); // find the level of the current node
				assert(level > 0);
				auto ctr = 0;
				for (int k = first_step_on_level(level - 1);
					k < first_step_on_level(level); k++) { // index of the second input source
					for (int j = 0; j < k; j++) { // the first input source that has a smaller index than the second one
						const auto sel_var = get_sel_var_n(spec2, i, ctr++, ispec);
						//ret &= add_simulation_clause_nc(spec2, t, i, j, k, 0, 0, 0, sel_var, ispec);
						ret &= add_simulation_clause_nc(spec2, t, i, j, k, 0, 0, 1, sel_var, ispec);
						ret &= add_simulation_clause_nc(spec2, t, i, j, k, 0, 1, 0, sel_var, ispec);
						ret &= add_simulation_clause_nc(spec2, t, i, j, k, 0, 1, 1, sel_var, ispec);
						ret &= add_simulation_clause_nc(spec2, t, i, j, k, 1, 0, 0, sel_var, ispec);
						ret &= add_simulation_clause_nc(spec2, t, i, j, k, 1, 0, 1, sel_var, ispec);
						ret &= add_simulation_clause_nc(spec2, t, i, j, k, 1, 1, 0, sel_var, ispec);
						ret &= add_simulation_clause_nc(spec2, t, i, j, k, 1, 1, 1, sel_var, ispec);
					}
				}
			}
			//assert(spec1.nr_steps <= spec1.nr_steps);
			//if (spec1.nr_steps < spec1.nr_steps) {

			for (int i = 0; i < spec2.nr_steps; i++) {
				// If an output has selected this particular operand, we
						// need to ensure that this operand's truth table satisfies
						// the specified output function.
				for (int h = 0; h < spec2.nr_nontriv; h++) {
					if (spec2.is_dont_care(h, t + 1)) {
						continue;
					}
					auto outbit = kitty::get_bit(
						spec2[spec2.synth_func(h)], t + 1);
					if ((spec2.out_inv >> spec2.synth_func(h)) & 1) {
						outbit = 1 - outbit;
					}
					pLits[0] = pabc::Abc_Var2Lit( get_out_var_n(spec2, h, i, ispec), 1);
					pLits[1] = pabc::Abc_Var2Lit( get_sim_var_n(spec2, i, t, ispec),
						1 - outbit);
					ret &= solver->add_clause(pLits, pLits + 2);
					if (spec2.verbosity > 2) {
						printf("creating oimp clause: ( ");
						printf("!g2_%d_%d \\/ %sx2_%d_%d ) (status=%d)\n",
							h + 1, // nontrive output number
							spec2.get_nr_in() + i + 1, // step number
							(1 - outbit) ? "!" : "",
							spec2.get_nr_in() + i + 1, // step number
							t + 2, // position in tt
							ret);
					}
				}
			}
			//}
			//ret &= fix_output_sim_vars_nc2(spec2, t, ispec);

			return ret;
		}

		void vcreate_tt_clauses(const spec& spec, int t)
		{
			for (int i = 0; i < spec.nr_steps; i++) {
				auto level = get_level(spec, i + spec.nr_in);
				assert(level > 0);
				auto ctr = 0;
				for (int k = first_step_on_level(level - 1);
					k < first_step_on_level(level); k++) {
					for (int j = 0; j < k; j++) {
						const auto sel_var = get_sel_var(spec, i, ctr++);
						add_simulation_clause(spec, t, i, j, k, 0, 0, 1, sel_var);
						add_simulation_clause(spec, t, i, j, k, 0, 1, 0, sel_var);
						add_simulation_clause(spec, t, i, j, k, 0, 1, 1, sel_var);
						add_simulation_clause(spec, t, i, j, k, 1, 0, 0, sel_var);
						add_simulation_clause(spec, t, i, j, k, 1, 0, 1, sel_var);
						add_simulation_clause(spec, t, i, j, k, 1, 1, 0, sel_var);
						add_simulation_clause(spec, t, i, j, k, 1, 1, 1, sel_var);
					}
				}
			}
			fix_output_sim_vars(spec, t);
		}

		void create_cardinality_constraints(const spec& spec)
		{
			std::vector<int> svars;
			std::vector<int> rvars;

			for (int i = 0; i < spec.nr_steps; i++) {
				svars.clear();
				rvars.clear();
				const auto level = get_level(spec, spec.nr_in + i);
				auto svar_ctr = 0;
				for (int k = first_step_on_level(level - 1);
					k < first_step_on_level(level); k++) {
					for (int j = 0; j < k; j++) {
						const auto sel_var = get_sel_var(spec, i, svar_ctr++);
						svars.push_back(sel_var);
					}
				}
				const int nr_res_vars = (1 + 2) * (svars.size() + 1);
				for (int j = 0; j < nr_res_vars; j++) {
					rvars.push_back(get_res_var(spec, i, j));
				}
				create_cardinality_circuit(solver, svars, rvars, 1);

				// Ensure that the fanin cardinality for each step i 
				// is exactly FI.
				const auto fi_var =
					get_res_var(spec, i, svars.size() * (1 + 2) + 1);
				auto fi_lit = pabc::Abc_Var2Lit(fi_var, 0);
				(void)solver->add_clause(&fi_lit, &fi_lit + 1);
			}
		}

		/// Ensure that each gate has 2 operands.
		bool create_fanin_clauses(const spec& spec)
		{
			bool res = true;
			for (int i = 0; i < spec.nr_steps; i++) {
				const auto nr_svars_for_i = nr_svars_for_step(spec, i);
				for (int j = 0; j < nr_svars_for_i; j++) {
					const auto sel_var = get_sel_var(spec, i, j);
					pabc::Vec_IntSetEntry(vLits, j, pabc::Abc_Var2Lit(sel_var, 0));
				}
				res &= solver->add_clause(pabc::Vec_IntArray(vLits),
					pabc::Vec_IntArray(vLits) + nr_svars_for_i);
			}
			return res;
		}

		/// Ensure that each gate has 2 operands.
		bool create_fanin_clauses_nc(const spec& spec)
		{
			bool res = true;
			for (int i = 0; i < spec.nr_steps; i++) {
				const auto nr_svars_for_i = nr_svars_for_step(spec, i);
				for (int j = 0; j < nr_svars_for_i; j++) {
					const auto sel_var = get_sel_var_n(spec, i, j, 0);
					pabc::Vec_IntSetEntry(vLits, j, pabc::Abc_Var2Lit(sel_var, 0));
				}
				res &= solver->add_clause(pabc::Vec_IntArray(vLits),
					pabc::Vec_IntArray(vLits) + nr_svars_for_i);
			}
			return res;
		}

		/// Add clauses which ensure that every step is used at least once.
		void create_alonce_clauses(const spec& spec)
		{
			for (int i = 0; i < spec.nr_steps - 1; i++) {
				auto ctr = 0;
				const auto level = get_level(spec, i + spec.nr_in);
				const auto idx = spec.nr_in + i;
				for (int ip = i + 1; ip < spec.nr_steps; ip++) {
					auto levelp = get_level(spec, ip + spec.nr_in);
					assert(levelp >= level);
					if (levelp == level) {
						continue;
					}
					auto svctr = 0;
					for (int k = first_step_on_level(levelp - 1);
						k < first_step_on_level(levelp); k++) {
						for (int j = 0; j < k; j++) {
							if (j != idx && k != idx) {
								svctr++;
								continue;
							}
							const auto sel_var = get_sel_var(spec, ip, svctr++);
							pabc::Vec_IntSetEntry(
								vLits,
								ctr++,
								pabc::Abc_Var2Lit(sel_var, 0));
						}
					}
				}
				solver->add_clause(pabc::Vec_IntArray(vLits), pabc::Vec_IntArray(vLits) + ctr);
			}
		}

		/// Add clauses which ensure that every step is used at least once.
		void create_alonce_clauses_nc(const spec& spec, int ispec)
		{
			for (int i = 0; i < spec.nr_steps - 1; i++) {
				auto ctr = 0;
				const auto level = get_level(spec, i + spec.nr_in);
				const auto idx = spec.nr_in + i;
				for (int ip = i + 1; ip < spec.nr_steps; ip++) {
					auto levelp = get_level(spec, ip + spec.nr_in);
					assert(levelp >= level);
					if (levelp == level) {
						continue;
					}
					auto svctr = 0;
					for (int k = first_step_on_level(levelp - 1);
						k < first_step_on_level(levelp); k++) {
						for (int j = 0; j < k; j++) {
							if (j != idx && k != idx) {
								svctr++;
								continue;
							}
							const auto sel_var = get_sel_var_n(spec, ip, svctr++, ispec);
							pabc::Vec_IntSetEntry(
								vLits,
								ctr++,
								pabc::Abc_Var2Lit(sel_var, 0));
						}
					}
				}
				solver->add_clause(pabc::Vec_IntArray(vLits), pabc::Vec_IntArray(vLits) + ctr);
			}

			for (int i = 0; i < spec.nr_in - 1; i++) {
				auto ctr = 0;
				const auto level = 1;
				const auto idx = i;
				for (int ip = 0; ip < spec.nr_steps; ip++) {
					auto levelp = get_level(spec, ip + spec.nr_in);
					assert(levelp >= level);
					if (levelp == level) {
						continue;
					}
					auto svctr = 0;
					for (int k = first_step_on_level(levelp - 1);
						k < first_step_on_level(levelp); k++) {
						for (int j = 0; j < k; j++) {
							if (j != idx && k != idx) {
								svctr++;
								continue;
							}
							const auto sel_var = get_sel_var_n(spec, ip, svctr++, ispec);
							pabc::Vec_IntSetEntry(
								vLits,
								ctr++,
								pabc::Abc_Var2Lit(sel_var, 0));
						}
					}
				}
				solver->add_clause(pabc::Vec_IntArray(vLits), pabc::Vec_IntArray(vLits) + ctr);
			}
		}

		/// Add clauses which ensure that every step is used at least once.
		void create_alonce_clauses_givenf(const spec& spec)
		{
			for (int i = 0; i < spec.nr_steps - 1; i++) {
				auto ctr = 0;
				const auto level = get_level(spec, i + spec.nr_in);
				if (level == get_level(spec, spec.nr_steps - 1 + spec.nr_in)) {
					continue;
				}
				const auto idx = spec.nr_in + i;
				for (int ip = i + 1; ip < spec.nr_steps; ip++) {
					auto levelp = get_level(spec, ip + spec.nr_in);
					assert(levelp >= level);
					if (levelp == level) {
						continue;
					}
					auto svctr = 0;
					for (int k = first_step_on_level(levelp - 1);
						k < first_step_on_level(levelp); k++) {
						for (int j = 0; j < k; j++) {
							if (j != idx && k != idx) {
								svctr++;
								continue;
							}
							const auto sel_var = get_sel_var(spec, ip, svctr++);
							pabc::Vec_IntSetEntry(
								vLits,
								ctr++,
								pabc::Abc_Var2Lit(sel_var, 0));
						}
					}
				}
				solver->add_clause(pabc::Vec_IntArray(vLits), pabc::Vec_IntArray(vLits) + ctr);
			}
		}

		bool add_simulation_clause(
			const spec& spec,
			const int t,
			const int i,
			const int j,
			const int k,
			const int a,
			const int b,
			const int c,
			int sel_var)
		{
			int pLits[5];
			int ctr = 0;

			if (j < spec.nr_in) {
				if ((((t + 1) & (1 << j)) ? 1 : 0) != b) {
					return true;
				}
			}
			else {
				pLits[ctr++] = pabc::Abc_Var2Lit(
					get_sim_var(spec, j - spec.nr_in, t), b);
			}

			if (k < spec.nr_in) {
				if ((((t + 1) & (1 << k)) ? 1 : 0) != c) {
					return true;
				}
			}
			else {
				pLits[ctr++] = pabc::Abc_Var2Lit(
					get_sim_var(spec, k - spec.nr_in, t), c);
			}

			pLits[ctr++] = pabc::Abc_Var2Lit(sel_var, 1);
			pLits[ctr++] = pabc::Abc_Var2Lit(get_sim_var(spec, i, t), a);

			if (b | c) {
				pLits[ctr++] = pabc::Abc_Var2Lit(
					get_op_var(spec, i, ((c << 1) | b) - 1), 1 - a);
			}

			if (spec.verbosity > 3) {
				printf("creating sim. clause: (");
				printf(" !s1_%d_%d ", spec.get_nr_in() + i + 1, (sel_var - 1) / 2 + 1);
				printf(" \\/ %sx1_%d_%d ", a ? "!" : "",
					spec.get_nr_in() + i + 1, t + 2);


				if (j >= spec.nr_in) {
					printf(" \\/ %sx1_%d_%d ",
						b ? "!" : "", (get_sim_var(spec, j - spec.nr_in, t) - b) / 2, t + 2);
				}
				if (j >= spec.nr_in) {
					printf(" \\/ %sx1_%d_%d ",
						c ? "!" : "", (get_sim_var(spec, k - spec.nr_in, t) - c) / 2, t + 2);
				}

				if (b | c) {
					printf(" \\/ %sf1_%d_%d ",
						1 - a ? "!" : "",
						spec.get_nr_in() + i + 1, ((c << 1) | b));
				}
				printf(") \n");
			}
			/*if (spec.verbosity > 2) {
				printf("Add clauses = ");
				for (int j = 0; j < ctr; j++) {
					if (j < ctr - 1) {
						printf("%d \\/ ", pLits[j]);
					}
					else if (j == ctr - 1) {
						printf("%d (POST)\n", pLits[j]);
					}
				}
			}*/
			return solver->add_clause(pLits, pLits + ctr);
		}
		bool add_simulation_clause_2c(
			const spec& spec,
			const int t,
			const int i,
			const int j,
			const int k,
			const int a,
			const int b,
			const int c,
			int sel_var)
		{
			int pLits[5];
			int ctr = 0;

			if (j < spec.nr_in) {
				if ((((t + 1) & (1 << j)) ? 1 : 0) != b) {
					return true;
				}
			}
			else {
				pLits[ctr++] = pabc::Abc_Var2Lit(
					total_nr_vars + get_sim_var(spec, j - spec.nr_in, t), b);
			}

			if (k < spec.nr_in) {
				if ((((t + 1) & (1 << k)) ? 1 : 0) != c) {
					return true;
				}
			}
			else {
				pLits[ctr++] = pabc::Abc_Var2Lit(
					total_nr_vars + get_sim_var(spec, k - spec.nr_in, t), c);
			}

			pLits[ctr++] = pabc::Abc_Var2Lit(sel_var, 1);
			pLits[ctr++] = pabc::Abc_Var2Lit(total_nr_vars + get_sim_var(spec, i, t), a);

			if (b | c) {
				pLits[ctr++] = pabc::Abc_Var2Lit(
					total_nr_vars + get_op_var(spec, i, ((c << 1) | b) - 1), 1 - a);
			}

			if (spec.verbosity > 3) {
				printf("creating sim. clause: (");
				printf(" !s2_%d_%d ", spec.get_nr_in() + i + 1, (sel_var - 1) / 2);
				printf(" \\/ %sx2_%d_%d ", a ? "!" : "",
					spec.get_nr_in() + i + 1, t + 2);


				if (j >= spec.nr_in) {
					printf(" \\/ %sx2_%d_%d ",
						b ? "!" : "", (get_sim_var(spec, j - spec.nr_in, t) - b) / 2, t + 2);
				}
				if (j >= spec.nr_in) {
					printf(" \\/ %sx2_%d_%d ",
						c ? "!" : "", (get_sim_var(spec, k - spec.nr_in, t) - c) / 2, t + 2);
				}

				if (b | c) {
					printf(" \\/ %sf2_%d_%d ",
						1 - a ? "!" : "",
						spec.get_nr_in() + i + 1, ((c << 1) | b));
				}
				printf(") \n");
			}
			return solver->add_clause(pLits, pLits + ctr);
		}
		bool add_simulation_clause_nc(
			const spec& spec,
			const int t, // primary output t-th bit
			const int i, // index of the current step
			const int j, // index of the first input
			const int k, // index of the second input
			const int a, // the t-th bit of the step i's output
			const int b, // the t-th bit of the step j's, first input
			const int c, // the t-th bit of the step k's, second input
			int sel_var,
			int ispec)
		{
			int pLits[5];
			int ctr = 0;

			if (j < spec.nr_in) {
				if ((((t + 1) & (1 << j)) ? 1 : 0) != b) {
					return true;
				}
			}
			else {
				pLits[ctr++] = pabc::Abc_Var2Lit(
					get_sim_var_n(spec, j - spec.nr_in, t, ispec), b);
			}

			if (k < spec.nr_in) {
				if ((((t + 1) & (1 << k)) ? 1 : 0) != c) {
					return true;
				}
			}
			else {
				pLits[ctr++] = pabc::Abc_Var2Lit(
					get_sim_var_n(spec, k - spec.nr_in, t, ispec), c);
			}

			pLits[ctr++] = pabc::Abc_Var2Lit(sel_var, 1);
			pLits[ctr++] = pabc::Abc_Var2Lit(get_sim_var_n(spec, i, t, ispec), a);

			if (b | c) {
				pLits[ctr++] = pabc::Abc_Var2Lit(
					get_op_var_n(spec, i, ((c << 1) | b) - 1, ispec), 1 - a);
			}

			if (spec.verbosity > 3) {
				printf("creating sim. clause: (");
				printf(" !s2_%d_%d ", spec.get_nr_in() + i + 1, (sel_var - 1) / 2);
				printf(" \\/ %sx2_%d_%d ", a ? "!" : "",
					spec.get_nr_in() + i + 1, t + 2);


				if (j >= spec.nr_in) {
					printf(" \\/ %sx2_%d_%d ",
						b ? "!" : "", (get_sim_var_n(spec, j - spec.nr_in, t, ispec) - b) / 2, t + 2);
				}
				if (j >= spec.nr_in) {
					printf(" \\/ %sx2_%d_%d ",
						c ? "!" : "", (get_sim_var_n(spec, k - spec.nr_in, t, ispec) - c) / 2, t + 2);
				}

				if (b | c) {
					printf(" \\/ %sf2_%d_%d ",
						1 - a ? "!" : "",
						spec.get_nr_in() + i + 1, ((c << 1) | b));
				}
				printf(") \n");
			}
			return solver->add_clause(pLits, pLits + ctr);
		}

		void create_noreapply_clauses(const spec& spec)
		{
			int pLits[3];

			// Disallow:
			// x_i : (j, k)
			// x_ip: (j, i) OR (k, i)
			for (int i = 0; i < spec.nr_steps; i++) {
				const auto idx = spec.nr_in + i;
				const auto level = get_level(spec, idx);

				for (int ip = i + 1; ip < spec.nr_steps; ip++) {
					const auto levelp = get_level(spec, ip +
						spec.nr_in);
					if (levelp == level) {
						// A node cannot have a node on the same level in
						// its fanin.
						continue;
					}

					auto svar_ctr = 0;
					for (int k = first_step_on_level(level - 1);
						k < first_step_on_level(level); k++) {
						for (int j = 0; j < k; j++) {
							const auto sel_var = get_sel_var(spec, i, svar_ctr++);
							pLits[0] = pabc::Abc_Var2Lit(sel_var, 1);

							// Note that it's possible for node ip to never have
							// i as its second fanin.
							auto svar_ctrp = 0;
							for (int kp = first_step_on_level(levelp - 1);
								kp < first_step_on_level(levelp); kp++) {
								for (int jp = 0; jp < kp; jp++) {
									if (kp == idx && (jp == j || jp == k)) {
										const auto sel_varp = get_sel_var(spec, ip, svar_ctrp);
										pLits[1] = pabc::Abc_Var2Lit(sel_varp, 1);
										auto status = solver->add_clause(pLits, pLits + 2);
										assert(status);
									}
									svar_ctrp++;
								}
							}
						}
					}
				}
			}

			// Disallow:
			// x_i  : (j, k)
			// x_ip : (j, k)
			// x_ipp: (i,ip)
			for (int i = 0; i < spec.nr_steps; i++) {
				const auto level = get_level(spec, spec.nr_in + i);

				for (int ip = i + 1; ip < spec.nr_steps; ip++) {
					const auto levelp = get_level(spec, ip + spec.nr_in);
					if (levelp != level) {
						// If they are not on the same level they 
						// cannot have the same fanin
						continue;
					}

					for (int ipp = ip + 1; ipp < spec.nr_steps; ipp++) {
						const auto levelpp = get_level(spec, ipp + spec.nr_in);
						if (levelpp == level) {
							continue;
						}

						auto svar_ctr = 0;
						for (int k = first_step_on_level(level - 1);
							k < first_step_on_level(level); k++) {
							for (int j = 0; j < k; j++) {
								auto svar_ctrpp = 0;
								for (int kpp = first_step_on_level(levelpp - 1);
									kpp < first_step_on_level(levelpp); kpp++) {
									for (int jpp = 0; jpp < kpp; jpp++) {
										if ((jpp == spec.nr_in + i) && (kpp == spec.nr_in + ip)) {
											const auto sel_var = get_sel_var(spec, i, svar_ctr);
											const auto sel_varp = get_sel_var(spec, ip, svar_ctr);
											const auto sel_varpp = get_sel_var(spec, ipp, svar_ctrpp);
											pLits[0] = pabc::Abc_Var2Lit(sel_var, 1);
											pLits[1] = pabc::Abc_Var2Lit(sel_varp, 1);
											pLits[2] = pabc::Abc_Var2Lit(sel_varpp, 1);
											(void)solver->add_clause(pLits, pLits + 3);
										}
										svar_ctrpp++;
									}
								}
								svar_ctr++;
							}
						}
					}
				}
			}
		}

		void create_noreapply_clauses_nc(const spec& spec)
		{
			int pLits[3];

			// Disallow:
			// x_i : (j, k)
			// x_ip: (j, i) OR (k, i)
			for (int i = 0; i < spec.nr_steps; i++) {
				const auto idx = spec.nr_in + i;
				const auto level = get_level(spec, idx);

				for (int ip = i + 1; ip < spec.nr_steps; ip++) {
					const auto levelp = get_level(spec, ip +
						spec.nr_in);
					if (levelp == level) {
						// A node cannot have a node on the same level in
						// its fanin.
						continue;
					}

					auto svar_ctr = 0;
					for (int k = first_step_on_level(level - 1);
						k < first_step_on_level(level); k++) {
						for (int j = 0; j < k; j++) {
							const auto sel_var = get_sel_var_n(spec, i, svar_ctr++, 0);
							pLits[0] = pabc::Abc_Var2Lit(sel_var, 1);

							// Note that it's possible for node ip to never have
							// i as its second fanin.
							auto svar_ctrp = 0;
							for (int kp = first_step_on_level(levelp - 1);
								kp < first_step_on_level(levelp); kp++) {
								for (int jp = 0; jp < kp; jp++) {
									if (kp == idx && (jp == j || jp == k)) {
										const auto sel_varp = get_sel_var_n(spec, ip, svar_ctrp, 0);
										pLits[1] = pabc::Abc_Var2Lit(sel_varp, 1);
										auto status = solver->add_clause(pLits, pLits + 2);
										assert(status);
									}
									svar_ctrp++;
								}
							}
						}
					}
				}
			}

			// Disallow:
			// x_i  : (j, k)
			// x_ip : (j, k)
			// x_ipp: (i,ip)
			for (int i = 0; i < spec.nr_steps; i++) {
				const auto level = get_level(spec, spec.nr_in + i);

				for (int ip = i + 1; ip < spec.nr_steps; ip++) {
					const auto levelp = get_level(spec, ip + spec.nr_in);
					if (levelp != level) {
						// If they are not on the same level they 
						// cannot have the same fanin
						continue;
					}

					for (int ipp = ip + 1; ipp < spec.nr_steps; ipp++) {
						const auto levelpp = get_level(spec, ipp + spec.nr_in);
						if (levelpp == level) {
							continue;
						}

						auto svar_ctr = 0;
						for (int k = first_step_on_level(level - 1);
							k < first_step_on_level(level); k++) {
							for (int j = 0; j < k; j++) {
								auto svar_ctrpp = 0;
								for (int kpp = first_step_on_level(levelpp - 1);
									kpp < first_step_on_level(levelpp); kpp++) {
									for (int jpp = 0; jpp < kpp; jpp++) {
										if ((jpp == spec.nr_in + i) && (kpp == spec.nr_in + ip)) {
											const auto sel_var = get_sel_var_n(spec, i, svar_ctr, 0);
											const auto sel_varp = get_sel_var_n(spec, ip, svar_ctr, 0);
											const auto sel_varpp = get_sel_var_n(spec, ipp, svar_ctrpp, 0);
											pLits[0] = pabc::Abc_Var2Lit(sel_var, 1);
											pLits[1] = pabc::Abc_Var2Lit(sel_varp, 1);
											pLits[2] = pabc::Abc_Var2Lit(sel_varpp, 1);
											(void)solver->add_clause(pLits, pLits + 3);
										}
										svar_ctrpp++;
									}
								}
								svar_ctr++;
							}
						}
					}
				}
			}
		}

		/// Extracts chain from encoded CNF solution.
		void extract_chain(const spec& spec, chain& chain) override
		{
			chain.reset(spec.nr_in, spec.get_nr_out(), spec.nr_steps, 2);

			kitty::dynamic_truth_table op(2);
			for (int i = 0; i < spec.nr_steps; i++) {
				for (int j = 0; j < OP_VARS_PER_STEP; j++) {
					if (solver->var_value(get_op_var(spec, i, j)))
						kitty::set_bit(op, j + 1);
					else
						kitty::clear_bit(op, j + 1);
				}

				if (spec.verbosity) {
					printf("  step x_%d performs operation\n  ",
						i + spec.nr_in + 1);
					kitty::print_binary(op, std::cout);
					printf("\n");
				}

				auto ctr = 0;
				const auto level = get_level(spec, spec.nr_in + i);
				for (int k = first_step_on_level(level - 1);
					k < first_step_on_level(level); k++) {
					for (int j = 0; j < k; j++) {
						const auto sel_var = get_sel_var(spec, i, ctr++);
						if (solver->var_value(sel_var)) {
							if (spec.verbosity) {
								printf("  with operands ");
								printf("x_%d ", j + 1);
								printf("x_%d ", k + 1);
							}
							chain.set_step(i, j, k, op);
							break;
						}
					}
				}

				if (spec.verbosity) {
					printf("\n");
				}
			}

			/*// TODO: support multiple outputs
			chain.set_output(0,
				((spec.nr_steps + spec.nr_in) << 1) +
				((spec.out_inv) & 1));*/
			auto triv_count = 0, nontriv_count = 0;
			for (int h = 0; h < spec.get_nr_out(); h++) {
				if ((spec.triv_flag >> h) & 1) {
					chain.set_output(h,
						(spec.triv_func(triv_count++) << 1) +
						((spec.out_inv >> h) & 1));
					continue;
				}
				for (int i = 0; i < spec.nr_steps; i++) {
					if (solver->var_value(get_out_var(spec, nontriv_count, i))) {
						chain.set_output(h,
							((i + spec.get_nr_in() + 1) << 1) +
							((spec.out_inv >> h) & 1));
						nontriv_count++;
						break;
					}
				}
			}
		}

		/// Extracts chain from encoded CNF solution.
		void extract_chain_2c(const spec& spec, chain& chain)
		{
			chain.reset(spec.nr_in, spec.get_nr_out(), spec.nr_steps, 2);

			kitty::dynamic_truth_table op(2);
			for (int i = 0; i < spec.nr_steps; i++) {
				for (int j = 0; j < OP_VARS_PER_STEP; j++) {
					if (solver->var_value(total_nr_vars + get_op_var(spec, i, j)))
						kitty::set_bit(op, j + 1);
					else
						kitty::clear_bit(op, j + 1);
				}

				if (spec.verbosity) {
					printf("  step x_%d performs operation\n  ",
						i + spec.nr_in + 1);
					kitty::print_binary(op, std::cout);
					printf("\n");
				}

				auto ctr = 0;
				const auto level = get_level(spec, spec.nr_in + i);
				for (int k = first_step_on_level(level - 1);
					k < first_step_on_level(level); k++) {
					for (int j = 0; j < k; j++) {
						const auto sel_var = get_sel_var(spec, i, ctr++);
						if (solver->var_value(sel_var)) {
							if (spec.verbosity) {
								printf("  with operands ");
								printf("x_%d ", j + 1);
								printf("x_%d ", k + 1);
							}
							chain.set_step(i, j, k, op);
							break;
						}
					}
				}

				if (spec.verbosity) {
					printf("\n");
				}
			}

			// TODO: support multiple outputs
			/*chain.set_output(0,
				((spec.nr_steps + spec.nr_in) << 1) +
				((spec.out_inv) & 1));*/
			auto triv_count = 0, nontriv_count = 0;
			for (int h = 0; h < spec.get_nr_out(); h++) {
				if ((spec.triv_flag >> h) & 1) {
					chain.set_output(h,
						(spec.triv_func(triv_count++) << 1) +
						((spec.out_inv >> h) & 1));
					continue;
				}
				for (int i = 0; i < spec.nr_steps; i++) {
					if (solver->var_value(total_nr_vars + get_out_var(spec, nontriv_count, i))) {
						chain.set_output(h,
							((i + spec.get_nr_in() + 1) << 1) +
							((spec.out_inv >> h) & 1));
						nontriv_count++;
						break;
					}
				}
			}
		}

		/// Extracts chain from encoded CNF solution.
		void extract_chain_nc(const spec& spec, chain& chain, int ispec)
		{
			chain.reset(spec.nr_in, spec.get_nr_out(), spec.nr_steps, 2);

			kitty::dynamic_truth_table op(2);
			for (int i = 0; i < spec.nr_steps; i++) {
				for (int j = 0; j < OP_VARS_PER_STEP; j++) {
					if (solver->var_value(get_op_var_n(spec, i, j, ispec)))
						kitty::set_bit(op, j + 1);
					else
						kitty::clear_bit(op, j + 1);
				}

				if (spec.verbosity) {
					printf("  step x_%d performs operation\n  ",
						i + spec.nr_in + 1);
					kitty::print_binary(op, std::cout);
					printf("\n");
				}

				auto ctr = 0;
				const auto level = get_level(spec, spec.nr_in + i);
				for (int k = first_step_on_level(level - 1);
					k < first_step_on_level(level); k++) {
					for (int j = 0; j < k; j++) {
						const auto sel_var = get_sel_var_n(spec, i, ctr++, ispec);
						if (solver->var_value(sel_var)) {
							if (spec.verbosity) {
								printf("  with operands ");
								printf("x_%d ", j + 1);
								printf("x_%d ", k + 1);
							}
							chain.set_step(i, j, k, op);
							break;
						}
					}
				}

				if (spec.verbosity) {
					printf("\n");
				}
			}

			// TODO: support multiple outputs
			/*chain.set_output(0,
				((spec.nr_steps + spec.nr_in) << 1) +
				((spec.out_inv) & 1));*/
			auto triv_count = 0, nontriv_count = 0;
			for (int h = 0; h < spec.get_nr_out(); h++) {
				if ((spec.triv_flag >> h) & 1) {
					chain.set_output(h,
						(spec.triv_func(triv_count++) << 1) +
						((spec.out_inv >> h) & 1));
					continue;
				}
				for (int i = 0; i < spec.nr_steps; i++) {
					if (solver->var_value(get_out_var_n(spec, nontriv_count, i, ispec))) {
						chain.set_output(h,
							((i + spec.get_nr_in() + 1) << 1) +
							((spec.out_inv >> h) & 1));
						nontriv_count++;
						break;
					}
				}
			}
		}
		std::vector <int> compare_vars(std::vector <int>& a, std::vector <int>& b)
		{
			std::vector <int> var_diff;
			int id = 0;
			for (int i = 0; i < a.size(); i++)
			{
				if (a[i] != b[i])
				{
					var_diff.push_back(i);
				}
			}
			return var_diff;
		}
		bool compare_boolean_chain(chain& chain0, chain& chain1)
		{
			int i;
			// check steps and operators
			if (chain0.get_nr_steps() != chain1.get_nr_steps())
				return success;
			for (i = 0; i < chain0.get_nr_steps(); i++)
			{
				for (int j = 0; j < 2; j++) {
					if (chain0.get_step(i)[j] != chain1.get_step(i)[j])
						return success;
				}
				int a = chain0.get_operator(i)._bits[0];
				int b = chain1.get_operator(i)._bits[0];
				if (chain0.get_operator(i)._bits[0] != chain1.get_operator(i)._bits[0])
					return success;
			}
			// check output
			std::vector <int > outputs0, outputs1;
			outputs0 = chain0.get_outputs();
			outputs1 = chain1.get_outputs();
			for (i = 0; i < chain0.get_nr_outputs(); i++)
			{
				if (outputs0[i] != outputs1[i])
					return success;
			}
			// the two chains are equivalent in circuitry level
			return failure;
		}

		/// Extracts chain from encoded CNF solution.
		void extract_chain_nc(const spec& spec, chain& chain, int ispec, std::vector<std::vector <int>>& rez)
		{
			// record the solution
			if (ispec == 0) {
				std::vector<int> res;
				rez.push_back(res);

				for (int ii = 0; ii < solver->nr_vars(); ii++)
				{
					rez[rez.size() - 1].push_back(solver->var_value(ii));
				}
			}

			chain.reset(spec.nr_in, spec.get_nr_out(), spec.nr_steps, 2);

			kitty::dynamic_truth_table op(2);
			for (int i = 0; i < spec.nr_steps; i++) {
				for (int j = 0; j < OP_VARS_PER_STEP; j++) {
					if (solver->var_value(get_op_var_n(spec, i, j, ispec)))
						kitty::set_bit(op, j + 1);
					else
						kitty::clear_bit(op, j + 1);
				}

				if (spec.verbosity) {
					printf("  step x_%d performs operation\n  ",
						i + spec.nr_in + 1);
					kitty::print_binary(op, std::cout);
					printf("\n");
				}

				auto ctr = 0;
				const auto level = get_level(spec, spec.nr_in + i);
				for (int k = first_step_on_level(level - 1);
					k < first_step_on_level(level); k++) {
					for (int j = 0; j < k; j++) {
						const auto sel_var = get_sel_var_n(spec, i, ctr++, ispec);
						if (solver->var_value(sel_var)) {
							if (spec.verbosity) {
								printf("  with operands ");
								printf("x_%d ", j + 1);
								printf("x_%d ", k + 1);
							}
							chain.set_step(i, j, k, op);
							break;
						}
					}
				}

				if (spec.verbosity) {
					printf("\n");
				}
			}

			// TODO: support multiple outputs
			/*chain.set_output(0,
				((spec.nr_steps + spec.nr_in) << 1) +
				((spec.out_inv) & 1));*/
			auto triv_count = 0, nontriv_count = 0;
			for (int h = 0; h < spec.get_nr_out(); h++) {
				if ((spec.triv_flag >> h) & 1) {
					chain.set_output(h,
						(spec.triv_func(triv_count++) << 1) +
						((spec.out_inv >> h) & 1));
					continue;
				}
				for (int i = 0; i < spec.nr_steps; i++) {
					if (solver->var_value(get_out_var_n(spec, nontriv_count, i, ispec))) {
						chain.set_output(h,
							((i + spec.get_nr_in() + 1) << 1) +
							((spec.out_inv >> h) & 1));
						nontriv_count++;
						break;
					}
				}
			}
		}

		void create_colex_clauses(const spec& spec)
		{
			int pLits[2];

			for (int i = 0; i < spec.nr_steps - 1; i++) {
				const auto level = get_level(spec, i + spec.nr_in);
				const auto levelp = get_level(spec, i + 1 + spec.nr_in);
				int svar_ctr = 0;
				for (int k = first_step_on_level(level - 1);
					k < first_step_on_level(level); k++) {
					for (int j = 0; j < k; j++) {
						if (k < 2) {
							svar_ctr++;
							continue;
						}
						const auto sel_var = get_sel_var(spec, i, svar_ctr);
						pLits[0] = pabc::Abc_Var2Lit(sel_var, 1);
						int svar_ctrp = 0;
						for (int kp = first_step_on_level(levelp - 1);
							kp < first_step_on_level(levelp); kp++) {
							for (int jp = 0; jp < kp; jp++) {
								if ((kp == k && jp < j) || (kp < k)) {
									const auto sel_varp = get_sel_var(spec, i + 1, svar_ctrp);
									pLits[1] = pabc::Abc_Var2Lit(sel_varp, 1);
									(void)solver->add_clause(pLits, pLits + 2);
								}
								svar_ctrp++;
							}
						}
						svar_ctr++;
					}
				}
			}
		}

		void create_colex_clauses_nc(const spec& spec)
		{
			int pLits[2];

			for (int i = 0; i < spec.nr_steps - 1; i++) {
				const auto level = get_level(spec, i + spec.nr_in);
				const auto levelp = get_level(spec, i + 1 + spec.nr_in);
				int svar_ctr = 0;
				for (int k = first_step_on_level(level - 1);
					k < first_step_on_level(level); k++) {
					for (int j = 0; j < k; j++) {
						if (k < 2) {
							svar_ctr++;
							continue;
						}
						const auto sel_var = get_sel_var_n(spec, i, svar_ctr, 0);
						pLits[0] = pabc::Abc_Var2Lit(sel_var, 1);
						int svar_ctrp = 0;
						for (int kp = first_step_on_level(levelp - 1);
							kp < first_step_on_level(levelp); kp++) {
							for (int jp = 0; jp < kp; jp++) {
								if ((kp == k && jp < j) || (kp < k)) {
									const auto sel_varp = get_sel_var_n(spec, i + 1, svar_ctrp, 0);
									pLits[1] = pabc::Abc_Var2Lit(sel_varp, 1);
									(void)solver->add_clause(pLits, pLits + 2);
								}
								svar_ctrp++;
							}
						}
						svar_ctr++;
					}
				}
			}
		}

		/*
				void
				create_colex_func_clauses(const spec& spec)
				{
					for (int i = 0; i < spec.nr_steps-1; i++) {
						for (int k = 1; k < spec.nr_in+i; k++) {
							for (int j = 0; j < k; j++) {
								pLits[0] = pabc::Abc_Var2Lit(spec.selection_vars[i][j][k], 1);
								pLits[1] = pabc::Abc_Var2Lit(spec.selection_vars[i+1][j][k], 1);

								pLits[2] =
									pabc::Abc_Var2Lit(get_op_var(spec, i, 1, 1), 1);
								pLits[3] =
									pabc::Abc_Var2Lit(get_op_var(spec, i+1, 1, 1), 0);
								solver_add_clause(this->solver, pLits, pLits+4);

								pLits[3] =
									pabc::Abc_Var2Lit(get_op_var(spec, i, 1, 0), 1);
								pLits[4] =
									pabc::Abc_Var2Lit(get_op_var(spec, i+1, 1, 1), 0);
								solver_add_clause(this->solver, pLits, pLits+5);
								pLits[4] =
									pabc::Abc_Var2Lit(get_op_var(spec, i+1, 1, 0), 0);
								solver_add_clause(this->solver, pLits, pLits+5);

								pLits[4] =
									pabc::Abc_Var2Lit(get_op_var(spec, i, 0, 1), 1);
								pLits[5] =
									pabc::Abc_Var2Lit(get_op_var(spec, i+1, 1, 1), 0);
								solver_add_clause(this->solver, pLits, pLits+6);
								pLits[5] =
									pabc::Abc_Var2Lit(get_op_var(spec, i+1, 1, 0), 0);
								solver_add_clause(this->solver, pLits, pLits+6);
								pLits[5] =
									pabc::Abc_Var2Lit(get_op_var(spec, i+1, 0, 1), 0);
								solver_add_clause(this->solver, pLits, pLits+6);
							}
						}
					}
				}
				*/

		void create_symvar_clauses(const spec& spec)
		{
			for (int q = 1; q < spec.nr_in; q++) {
				for (int p = 0; p < q; p++) {
					auto symm = true;
					for (int i = 0; i < spec.nr_nontriv; i++) {
						auto& f = spec[spec.synth_func(i)];
						if (!(swap(f, p, q) == f)) {
							symm = false;
							break;
						}
					}
					if (!symm) {
						continue;
					}
					for (int i = 1; i < spec.nr_steps; i++) {
						const auto level = get_level(spec, i + spec.nr_in);
						int svar_ctr = 0;
						for (int k = first_step_on_level(level - 1);
							k < first_step_on_level(level); k++) {
							for (int j = 0; j < k; j++) {
								if (!(j == q || k == q) || j == p) {
									svar_ctr++;
									continue;
								}
								const auto sel_var = get_sel_var(spec, i, svar_ctr);
								pabc::Vec_IntSetEntry(vLits, 0, pabc::Abc_Var2Lit(sel_var, 1));
								auto ctr = 1;
								for (int ip = 0; ip < i; ip++) {
									const auto levelp = get_level(spec, spec.nr_in + ip);
									auto svar_ctrp = 0;
									for (int kp = first_step_on_level(levelp - 1);
										kp < first_step_on_level(levelp); kp++) {
										for (int jp = 0; jp < kp; jp++) {
											if (jp == p || kp == p) {
												const auto sel_varp = get_sel_var(spec, ip, svar_ctrp);
												pabc::Vec_IntSetEntry(vLits, ctr++,
													pabc::Abc_Var2Lit(sel_varp, 0));
											}
											svar_ctrp++;
										}
									}
								}
								(void)solver->add_clause(Vec_IntArray(vLits), Vec_IntArray(vLits) + ctr);
								svar_ctr++;
							}
						}
					}
				}
			}
		}

		void create_symvar_clauses_nc(const spec& spec)
		{
			for (int q = 1; q < spec.nr_in; q++) {
				for (int p = 0; p < q; p++) {
					auto symm = true;
					for (int i = 0; i < spec.nr_nontriv; i++) {
						auto& f = spec[spec.synth_func(i)];
						if (!(swap(f, p, q) == f)) {
							symm = false;
							break;
						}
					}
					if (!symm) {
						continue;
					}
					for (int i = 1; i < spec.nr_steps; i++) {
						const auto level = get_level(spec, i + spec.nr_in);
						int svar_ctr = 0;
						for (int k = first_step_on_level(level - 1);
							k < first_step_on_level(level); k++) {
							for (int j = 0; j < k; j++) {
								if (!(j == q || k == q) || j == p) {
									svar_ctr++;
									continue;
								}
								const auto sel_var = get_sel_var_n(spec, i, svar_ctr, 0);
								pabc::Vec_IntSetEntry(vLits, 0, pabc::Abc_Var2Lit(sel_var, 1));
								auto ctr = 1;
								for (int ip = 0; ip < i; ip++) {
									const auto levelp = get_level(spec, spec.nr_in + ip);
									auto svar_ctrp = 0;
									for (int kp = first_step_on_level(levelp - 1);
										kp < first_step_on_level(levelp); kp++) {
										for (int jp = 0; jp < kp; jp++) {
											if (jp == p || kp == p) {
												const auto sel_varp = get_sel_var_n(spec, ip, svar_ctrp, 0);
												pabc::Vec_IntSetEntry(vLits, ctr++,
													pabc::Abc_Var2Lit(sel_varp, 0));
											}
											svar_ctrp++;
										}
									}
								}
								(void)solver->add_clause(Vec_IntArray(vLits), Vec_IntArray(vLits) + ctr);
								svar_ctr++;
							}
						}
					}
				}
			}
		}

		/// Encodes specifciation for use in fence-based synthesis flow.
		bool encode(const spec& spec, const fence& f) override
		{
			assert(spec.nr_steps == f.nr_nodes());

			bool success = true;

			update_level_map(spec, f);
			create_variables(spec);
			success = create_main_clauses(spec);
			if (!success) {
				return false;
			}

			if (!create_output_clauses(spec)) {
				return false;
			}

			if (!create_fanin_clauses(spec)) {
				return false;
			}

			if (spec.is_primitive_set()) {
				if (!create_primitive_clauses(spec))
					return false;
			}
			else if (spec.add_nontriv_clauses) {
				create_nontriv_clauses(spec);
			}

			/*if (spec.add_alonce_clauses) {
				create_alonce_clauses_givenf(spec);
			}*/
			if (spec.add_noreapply_clauses) {
				create_noreapply_clauses(spec);
			}
			if (spec.add_colex_clauses) {
				create_colex_clauses(spec);
			}
			/*
			if (spec.add_colex_func_clauses) {
				create_colex_func_clauses(spec);
			}
*/
			if (spec.add_symvar_clauses) {
				create_symvar_clauses(spec);
			}

			return true;
		}

		/// Given two netlists, Encodes specifciation for use in fence-based synthesis flow.
		bool encode_nc(const std::vector<spec> spec_all, const fence& f)
		{
			/*for (int i = 0; i < spec_all.size(); i++) {
				assert(spec_all[i].nr_steps == f.nr_nodes());
			}*/

			bool success = true;

			update_level_map(spec_all[0], f); // accumulated node number by layer
			create_variables_nc(spec_all); // create the variable space for the potential circuit
			// 1c is directly combine the output clauses of two circuits
			// 1c2 is with output clauses of two circuits seperated
			/*success = create_main_clauses_1c2(spec_all[0]);
			if (!success) {
				return false;
			}*/
			for (int i = 0; i < spec_all.size(); i++) {
				success = create_main_clauses_nc2(spec_all[i], i);
				if (!success) {
					return false;
				}
			}

			//create_sameout_clauses_nc(spec_all);

			if (!create_output_clauses_nc(spec_all)) {
				return false;
			}

			if (!create_fanin_clauses_nc(spec_all[0])) { // only related to sel
				return false;
			}

			for (int i = 0; i < spec_all.size(); i++) {
				if (spec_all[i].is_primitive_set()) {
					if (!create_primitive_clauses_nc2(spec_all[i], i))
						return false;
				}
				//else if (spec_all[i].add_nontriv_clauses) { //do not allow trivial operators
					//create_nontriv_clauses_nc(spec_all[i]);
				//}
				if (spec_all[i].add_alonce_clauses) { // all steps must be used at least once (only related to sel)
					create_alonce_clauses_nc(spec_all[i], i);
				}
			}

			/*if (spec_all[0].add_noreapply_clauses) { // no re-application of operators (only related to sel)
				create_noreapply_clauses_nc(spec_all[0]);
			}*/

			if (spec_all[0].add_colex_clauses) { // order step fanins co-lexicographically (only related to sel)
				create_colex_clauses_nc(spec_all[0]);
			}

			if (spec_all[0].add_symvar_clauses) { // impose order on symmetric variables (related to both func and sel)
				create_symvar_clauses_nc(spec_all[0]);
			}
			return true;
		}

		/// Given two netlists, Encodes specifciation for use in fence-based synthesis flow.
		bool encode_nc_abc(const std::vector<spec> spec_all, const fence& f, std::vector<std::vector<int>>& rez)
		{
			/*for (int i = 0; i < spec_all.size(); i++) {
				assert(spec_all[i].nr_steps == f.nr_nodes());
			}*/

			bool success = true;

			update_level_map(spec_all[0], f); // accumulated node number by layer
			create_variables_nc(spec_all); // create the variable space for the potential circuit
			// 1c is directly combine the output clauses of two circuits
			// 1c2 is with output clauses of two circuits seperated
			/*success = create_main_clauses_1c2(spec_all[0]);
			if (!success) {
				return false;
			}*/
			for (int i = 0; i < spec_all.size(); i++) {
				success = create_main_clauses_nc2(spec_all[i], i);
				if (!success) {
					return false;
				}
			}

			//create_sameout_clauses_nc(spec_all);

			if (!create_output_clauses_nc(spec_all)) {
				return false;
			}

			if (!create_fanin_clauses_nc(spec_all[0])) { // only related to sel
				return false;
			}

			for (int i = 0; i < spec_all.size(); i++) {
				if (spec_all[i].is_primitive_set()) {
					if (!create_primitive_clauses_nc2(spec_all[i], i))
						return false;
				}
				else if (spec_all[i].add_nontriv_clauses) {
					create_nontriv_clauses_nc2(spec_all[i]);
				}
				if (spec_all[i].add_alonce_clauses) { // all steps must be used at least once (only related to sel)
					create_alonce_clauses_nc(spec_all[i], i);
				}
			}

			/*if (spec1.add_alonce_clauses) { // only related to sel
				create_alonce_clauses(spec1);
			}*/

			/*if (spec_all[0].add_noreapply_clauses) { // only related to sel
				create_noreapply_clauses_nc(spec_all[0]);
			}*/

			if (spec_all[0].add_colex_clauses) { // only related to sel
				create_colex_clauses_nc(spec_all[0]);
			}

			/*
			if (spec.add_colex_func_clauses) {
				create_colex_func_clauses(spec);
			}
*/
			if (spec_all[0].add_symvar_clauses) { // related to both sel
				create_symvar_clauses_nc(spec_all[0]);
			}
			/*if (spec1.add_symvar_clauses) {
				create_symvar_clauses_2c(spec1);
			}*/
			//create_variables(spec2);
			if (rez.size() > 0)
			{
				for (int ires = 0; ires < rez.size(); ires++)
				{
					create_removerez_clauses_nc(spec_all, rez[ires]);
				}
			}

			return true;
		}

		/// Given two netlists, Encodes specifciation for use in fence-based synthesis flow.
		bool encode_2c(const spec& spec1, const spec& spec2, const fence& f)
		{
			/*for (int i = 0; i < spec_all.size(); i++) {
				assert(spec_all[i].nr_steps == f.nr_nodes());
			}*/

			bool success = true;

			update_level_map(spec1, f);
			create_variables_2c(spec1, spec2);
			// 1c is directly combine the output clauses of two circuits
			// 1c2 is with output clauses of two circuits seperated
			success = create_main_clauses_1c2(spec1);
			if (!success) {
				return false;
			}
			success = create_main_clauses_2c2(spec2);
			if (!success) {
				return false;
			}

			create_sameout_clauses(spec1, spec2);

			if (!create_output_clauses(spec1)) {
				return false;
			}
			if (!create_output_clauses_2c(spec2)) {
				return false;
			}

			if (!create_fanin_clauses(spec1)) { // only related to sel
				return false;
			}

			if (spec1.is_primitive_set()) {
				if (!create_primitive_clauses(spec1))
					return false;
			}
			else if (spec1.add_nontriv_clauses) {
				create_nontriv_clauses(spec1);
			}

			if (spec1.is_primitive_set()) {
				if (!create_primitive_clauses_2c(spec2))
					return false;
			}
			else if (spec1.add_nontriv_clauses) {
				create_nontriv_clauses_2c(spec2);
			}

			/*if (spec1.add_alonce_clauses) { // only related to sel
				create_alonce_clauses(spec1);
			}*/

			if (spec1.add_noreapply_clauses) { // only related to sel
				create_noreapply_clauses(spec1);
			}

			if (spec1.add_colex_clauses) { // only related to sel
				create_colex_clauses(spec1);
			}

			/*
			if (spec.add_colex_func_clauses) {
				create_colex_func_clauses(spec);
			}
*/
			if (spec1.add_symvar_clauses) { // related to both func and sel
				create_symvar_clauses(spec1);
			}
			/*if (spec1.add_symvar_clauses) {
				create_symvar_clauses_2c(spec1);
			}*/
			//create_variables(spec2);

			return true;
		}
		bool encode_1c(const spec& spec1, const spec& spec2, const fence& f)
		{
			assert(spec1.nr_steps == f.nr_nodes());

			bool success = true;

			update_level_map(spec1, f);
			//create_variables(spec1);
			success = create_main_clauses(spec1);
			if (!success) {
				return false;
			}

			if (!create_fanin_clauses(spec1)) {
				return false;
			}

			if (spec1.is_primitive_set()) {
				if (!create_primitive_clauses(spec1))
					return false;
			}
			else if (spec1.add_nontriv_clauses) {
				create_nontriv_clauses(spec1);
			}

			if (spec1.add_alonce_clauses) {
				create_alonce_clauses(spec1);
			}
			if (spec1.add_noreapply_clauses) {
				create_noreapply_clauses(spec1);
			}
			if (spec1.add_colex_clauses) {
				create_colex_clauses(spec1);
			}
			/*
			if (spec.add_colex_func_clauses) {
				create_colex_func_clauses(spec);
			}
*/
			if (spec1.add_symvar_clauses) {
				create_symvar_clauses(spec1);
			}
			//create_variables(spec2);

			return true;
		}

		/// Encodes specifciation for use in CEGAR based synthesis flow.
		bool cegar_encode(const spec& spec, const fence& f) override
		{
			assert(spec.nr_steps == f.nr_nodes());

			update_level_map(spec, f);
			cegar_create_variables(spec);

			if (!create_fanin_clauses(spec)) {
				return false;
			}
			create_cardinality_constraints(spec);

			if (spec.add_nontriv_clauses) {
				create_nontriv_clauses(spec);
			}
			if (spec.add_alonce_clauses) {
				create_alonce_clauses(spec);
			}
			if (spec.add_noreapply_clauses) {
				create_noreapply_clauses(spec);
			}
			if (spec.add_colex_clauses) {
				create_colex_clauses(spec);
			}
			/*
			if (spec.add_colex_func_clauses) {
				create_colex_func_clauses(spec);
			}
			*/
			if (spec.add_symvar_clauses) {
				create_symvar_clauses(spec);
			}

			return true;
		}

		/// Assumes that a solution has been found by the current encoding.
		/// Blocks the current solution such that the solver is forced to
		/// find different ones (if they exist).
		/*
		bool block_solution(const spec& spec)
		{
			// TODO: implement!
			return false;
		}


		/// Similar to block_solution, but blocks all solutions with the
		/// same structure. This is more restrictive, since the other
		/// method allows for the same structure but different operators.
		bool block_struct_solution(const spec& spec)
		{
			// TODO: implement!
			return false;
		}
		*/

		kitty::dynamic_truth_table& simulate(const spec& spec) override
		{
			int op_inputs[2] = { 0, 0 };

			for (int i = 0; i < spec.nr_steps; i++) {
				char op = 0;
				if (solver->var_value(get_op_var(spec, i, 0))) {
					op |= (1 << 1);
				}
				if (solver->var_value(get_op_var(spec, i, 1))) {
					op |= (1 << 2);
				}
				if (solver->var_value(get_op_var(spec, i, 2))) {
					op |= (1 << 3);
				}

				auto ctr = 0;
				auto brk = false;
				const auto level = get_level(spec, spec.nr_in + i);
				for (int k = first_step_on_level(level - 1);  // find the inputs of a step
					k < first_step_on_level(level) && !brk; k++) {
					for (int j = 0; j < k && !brk; j++) {
						const auto sel_var = get_sel_var(spec, i, ctr++);
						if (solver->var_value(sel_var)) {
							op_inputs[0] = j;
							op_inputs[1] = k;
							brk = true;
						}
					}
				}

				auto& tt_step = sim_tts[spec.nr_in + i];
				switch (op) {
				case 2: // x1^(~x2)
					tt_step = sim_tts[op_inputs[0]] & (~sim_tts[op_inputs[1]]);
					break;
				case 4: // (~x1)^x2
					tt_step = (~sim_tts[op_inputs[0]]) & sim_tts[op_inputs[1]];
					break;
				case 6: // XOR
					tt_step = sim_tts[op_inputs[0]] ^ sim_tts[op_inputs[1]];
					break;
				case 8: // AND
					tt_step = sim_tts[op_inputs[0]] & sim_tts[op_inputs[1]];
					break;
				case 14: // OR
					tt_step = sim_tts[op_inputs[0]] | sim_tts[op_inputs[1]];
					break;
				default:
					fprintf(stderr, "Error: unknown operator\n");
					assert(false);
					exit(1);
				}
			}

			return sim_tts[spec.nr_in + spec.nr_steps - 1];
		}

		void reset_sim_tts(int nr_in) override
		{
			for (int i = 0; i < NR_SIM_TTS; i++) {
				sim_tts[i] = kitty::dynamic_truth_table(nr_in);
				if (i < nr_in) {
					kitty::create_nth_var(sim_tts[i], i);
				}
			}
		}

		bool create_primitive_clauses(const spec& spec)
		{
			const auto primitives = spec.get_compiled_primitives();

			if (primitives.size() == 1) {
				const auto op = primitives[0];
				for (int i = 0; i < spec.nr_steps; i++) {
					for (int j = 1; j <= nr_op_vars_per_step; j++) {
						const auto op_var = get_op_var(spec, i, j);
						auto op_lit = pabc::Abc_Var2Lit(op_var, 1 - kitty::get_bit(op, j));
						const auto status = solver->add_clause(&op_lit, &op_lit + 1);
						if (!status) {
							return false;
						}
					}
				}
			}
			else {
				kitty::dynamic_truth_table tt(spec.fanin);
				kitty::clear(tt);
				do {
					if (!is_normal(tt)) {
						kitty::next_inplace(tt);
						continue;
					}
					bool is_primitive_operator = false;
					for (const auto& primitive : primitives) {
						if (primitive == tt) {
							is_primitive_operator = true;
						}
					}
					if (!is_primitive_operator) {
						for (int i = 0; i < spec.nr_steps; i++) {
							for (int j = 1; j <= nr_op_vars_per_step; j++) {
								pabc::Vec_IntSetEntry(vLits, j - 1,
									pabc::Abc_Var2Lit(get_op_var(spec, i, j - 1),
										kitty::get_bit(tt, j)));
							}
							const auto status = solver->add_clause(
								pabc::Vec_IntArray(vLits),
								pabc::Vec_IntArray(vLits) + nr_op_vars_per_step);
							if (!status) {
								return false;
							}
						}
					}
					kitty::next_inplace(tt);
				} while (!kitty::is_const0(tt));
			}

			return true;
		}

		bool create_primitive_clauses_2c(const spec& spec)
		{
			const auto primitives = spec.get_compiled_primitives();

			if (primitives.size() == 1) {
				const auto op = primitives[0];
				for (int i = 0; i < spec.nr_steps; i++) {
					for (int j = 1; j <= nr_op_vars_per_step; j++) {
						const auto op_var = total_nr_vars + get_op_var(spec, i, j);
						auto op_lit = pabc::Abc_Var2Lit(op_var, 1 - kitty::get_bit(op, j));
						const auto status = solver->add_clause(&op_lit, &op_lit + 1);
						if (!status) {
							return false;
						}
					}
				}
			}
			else {
				kitty::dynamic_truth_table tt(spec.fanin);
				kitty::clear(tt);
				do {
					if (!is_normal(tt)) {
						kitty::next_inplace(tt);
						continue;
					}
					bool is_primitive_operator = false;
					for (const auto& primitive : primitives) {
						if (primitive == tt) {
							is_primitive_operator = true;
						}
					}
					if (!is_primitive_operator) {
						for (int i = 0; i < spec.nr_steps; i++) {
							for (int j = 1; j <= nr_op_vars_per_step; j++) {
								pabc::Vec_IntSetEntry(vLits, j - 1,
									pabc::Abc_Var2Lit(total_nr_vars + get_op_var(spec, i, j - 1),
										kitty::get_bit(tt, j)));
							}
							const auto status = solver->add_clause(
								pabc::Vec_IntArray(vLits),
								pabc::Vec_IntArray(vLits) + nr_op_vars_per_step);
							if (!status) {
								return false;
							}
						}
					}
					kitty::next_inplace(tt);
				} while (!kitty::is_const0(tt));
			}

			return true;
		}

		bool create_primitive_clauses_nc(const spec& spec)
		{
			const auto primitives = spec.get_compiled_primitives();
			if (primitives.size() == 1) {
				const auto op = primitives[0];
				for (int i = 0; i < spec.nr_steps; i++) {
					for (int j = 1; j <= nr_op_vars_per_step; j++) {
						const auto op_var = total_nr_vars + get_op_var_n(spec, i, j, 0);
						auto op_lit = pabc::Abc_Var2Lit(op_var, 1 - kitty::get_bit(op, j));
						const auto status = solver->add_clause(&op_lit, &op_lit + 1);
						if (!status) {
							return false;
						}
					}
				}
			}
			else {
				kitty::dynamic_truth_table tt(spec.fanin);
				kitty::clear(tt);
				do {
					if (!is_normal(tt)) {
						kitty::next_inplace(tt);
						continue;
					}
					bool is_primitive_operator = false;
					for (const auto& primitive : primitives) {
						if (primitive == tt) {
							is_primitive_operator = true;
						}
					}
					if (!is_primitive_operator) {
						for (int i = 0; i < spec.nr_steps; i++) {
							for (int j = 1; j <= nr_op_vars_per_step; j++) {
								pabc::Vec_IntSetEntry(vLits, j - 1,
									pabc::Abc_Var2Lit(get_op_var_n(spec, i, j - 1, 0),
										kitty::get_bit(tt, j)));
							}
							const auto status = solver->add_clause(
								pabc::Vec_IntArray(vLits),
								pabc::Vec_IntArray(vLits) + nr_op_vars_per_step);
							if (!status) {
								return false;
							}
						}
					}
					kitty::next_inplace(tt);
				} while (!kitty::is_const0(tt));
			}
			return true;
		}
		bool create_primitive_clauses_nc2(const spec& spec, const int ispec)
		{
			const auto primitives = spec.get_compiled_primitives();
			if (primitives.size() == 1) {
				const auto op = primitives[0];
				for (int i = 0; i < spec.nr_steps; i++) {
					for (int j = 1; j <= nr_op_vars_per_step; j++) {
						const auto op_var = get_op_var_n(spec, i, j, ispec);
						auto op_lit = pabc::Abc_Var2Lit(op_var, 1 - kitty::get_bit(op, j));
						const auto status = solver->add_clause(&op_lit, &op_lit + 1);
						if (!status) {
							return false;
						}
					}
				}
			}
			else {
				kitty::dynamic_truth_table tt(spec.fanin);
				kitty::clear(tt);
				do {
					if (!is_normal(tt)) {
						kitty::next_inplace(tt);
						continue;
					}
					bool is_primitive_operator = false;
					for (const auto& primitive : primitives) {
						if (primitive == tt) {
							is_primitive_operator = true;
						}
					}
					if (!is_primitive_operator) {
						for (int i = 0; i < spec.nr_steps; i++) {
							for (int j = 1; j <= nr_op_vars_per_step; j++) {
								pabc::Vec_IntSetEntry(vLits, j - 1,
									pabc::Abc_Var2Lit(get_op_var_n(spec, i, j - 1, ispec),
										kitty::get_bit(tt, j)));
							}
							const auto status = solver->add_clause(
								pabc::Vec_IntArray(vLits),
								pabc::Vec_IntArray(vLits) + nr_op_vars_per_step);
							if (!status) {
								return false;
							}
						}
					}
					kitty::next_inplace(tt);
				} while (!kitty::is_const0(tt));
			}
			return true;
		}
	};
}

