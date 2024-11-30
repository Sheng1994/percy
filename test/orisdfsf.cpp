#include <cstdio>
#include <percy/percy.hpp>
#include <ctime>
#include <fstream>
#include <string>
#include <iostream>
#include <sys/stat.h>
#include <sys/types.h>


#define MAX_TESTS 256

using namespace percy;
using kitty::dynamic_truth_table;

int main()
{
	bsat_wrapper solver;
	partial_dag_encoder encoder(solver);
	partial_dag g;
	std::vector<int> settings;
	int ctrl_length = 4;
	settings = read_settings_txt("Synthesis_Settings.txt"); // InputNum OutputNum NodeNum
	parse_setting4dag(g, settings, ctrl_length);
	std::vector<std::string> tts_all;
	tts_all = read_tts("truth_tables.txt");
	chain c0;
	spec spec0;
		

	spec0.nr_in = settings[0]; fprintf(stdout, "Intput number of circuit: %d\n", spec0.nr_in);
	spec0.out_width = settings[1]; fprintf(stdout, "Total function number of circuit: %d\n", spec0.out_width);
	spec0.nr_out = settings[2]; fprintf(stdout, "Output number of circuit: %d\n", spec0.nr_out);
	spec0.verbosity = 0; 
	spec0.fanin = 2;  fprintf(stdout, "Intput number of nodes: %d\n", spec0.fanin);
	spec0.initial_steps = g.nr_vertices();
	spec0.set_primitive(CUST); // use customized primitives 'CUST'
	for (auto inet = 0; inet < spec0.nr_out; inet++) { // how many outputs per circuit
		kitty::dynamic_truth_table tt(spec0.nr_in);
		kitty::create_from_hex_string(tt, tts_all[inet]);
		spec0[inet] = tt;
	}
	auto res = failure;
	const auto start0 = std::clock();
	spec0.verbosity = 0;
	res = pd_synthesize_mo(spec0, c0, g, solver, encoder);
	if (res == success) {
		write_chain_LUT(c0, tts_all, "Synthesis_result.txt"); 
		fprintf(stdout, "The resulted net is written\n");

		auto sim_fs_f = c0.simulate();
		for (int i = 0; i < spec0.get_nr_out(); i++)
		{
			if (!(sim_fs_f[i] == spec0[i]))
			{
				fprintf(stdout, "An incorrect result generated at %d-th output\n", i+1);
				fprintf(stdout, "Synthesis succeeded but truth table check failed\n");
				std::string input = "Synthesis failed:\ntruth table check failed";
				std::ofstream out("Synthesis_log.txt");
				out << input;
				out.close();
				abort();
			}
		}
		fprintf(stdout, "Synthesis succeeded\n");
		std::string input;
		if (spec0.nr_triv == spec0.get_nr_out()) {
			input = "All functions are trivial\n";
		}
		else {
			input = "Synthesis succeeded\n";
		}
		std::ofstream out("Synthesis_log.txt");
		out << input;
		char buffer[30];
		for (int h = 0; h < spec0.get_nr_out(); h++) {
			if ((1 & (spec0.triv_flag >> h)) == 1)
			{
				sprintf(buffer, "function %d is trivial\n", h);
				out << buffer;
			}
		}
		out.close();
	}
	else {
		fprintf(stdout, "-1\n");
		//fprintf("Synthesis failed at nr_nodes=%d", nr_node_);
		std::string input = ("Synthesis failed");
		std::ofstream out("Synthesis_log.txt");
		out << input;
		out.close();
	}
	fprintf(stdout, "Successfully ended\n");
}
