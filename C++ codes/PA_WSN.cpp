#include "pch.h"

/*header files in the Boost library: https://www.boost.org/*/
#include <iostream>
#include <fstream>
#include <boost/numeric/ublas/vector.hpp>
#include <boost/numeric/ublas/vector_proxy.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <ctime>
#include <cstdlib>
#include <chrono>
#include <boost/graph/connected_components.hpp>
#include <boost/numeric/ublas/matrix.hpp>
#include <boost/numeric/ublas/matrix_proxy.hpp>
#include <boost/numeric/ublas/lu.hpp>
#include <boost/numeric/ublas/io.hpp>
#include <boost/heap/pairing_heap.hpp> // pairing_heap uses less memory
#include <boost/graph/prim_minimum_spanning_tree.hpp>
#include <boost/random.hpp>
#include <cstdint>
#include <boost/thread.hpp>
#include <boost/chrono.hpp>
#include <boost/thread/scoped_thread.hpp>



/*header files in the YS-Graph-Library: https://github.com/YahuiSun/YS-Graph-Library*/
#include <boost_graph.h>
#include <boost_graph_print_nw.h>
#include <boost_graph_print_all_edges.h>
#include <boost_graph_transform_ec_nw_back.h>
#include <boost_graph_is_a_tree_ignore_isolated_vertices.h>
#include <boost_graph_find_MST.h>
#include <boost_graph_MST_postprocessing.h>
#include <boost_graph_count_connected_cpn_Vsize.h>
#include <boost_graph_sum_of_nw_and_ec.h>
#include <convert_number_to_array_of_binary.h>
#include <copy_items.h>
#include <read_csv.h>
#include <parse_string.h>
#include <print_items.h>
#include <string_is_number.h>




using namespace std;
using namespace boost::heap;
using namespace boost::numeric::ublas; // there is a vector file inside which conflicts with std; so use std::vector to specify the vector definition



/*universal functions*/

#pragma region

double net_cost_KleinNWSTP(graph& input_graph, std::vector<int>& terminal) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;

	double included_cost = 0;
	int N = num_vertices(input_graph); // number of vertices


	for (int i = 0; i < N; i++) {
		if (in_degree(i, input_graph) > 0 && terminal[i] == 0) {
			included_cost = included_cost + get(boost::vertex_name_t(), input_graph, i); // included nw
		}
		boost::tie(ai, a_end) = boost::adjacent_vertices(i, input_graph);
		for (; ai != a_end; ai++) {
			if (*ai > i) {
				included_cost = included_cost + 
					get(boost::edge_weight_t(), input_graph, boost::edge(i, *ai, input_graph).first);// included ec
			}
		}
	}

	return included_cost;
}

#pragma endregion net_cost_KleinNWSTP 

#pragma region 
bool meet_constraints_of_terminal_and_leafterminal
(graph& solution_graph, std::vector<int>& terminal, std::vector<int>& leaf_terminal) {

	for (int i = 0; i < num_vertices(solution_graph); i++) {
		if (terminal[i] == 1) {
			if (in_degree(i, solution_graph) == 0) { // assumed there is at least one edge
				cout << "terminal is not in solution!" << endl;
				return false;
			}
			if (leaf_terminal[i] == 1) {
				if (in_degree(i, solution_graph) > 1) {
					cout << "leaf_terminal is not a leaf in solution!" << endl;
					return false;
				}
			}
		}
	}

	return true;

}
#pragma endregion meet_constraints_of_terminal_and_leafterminal 

#pragma region
void transform_NWPFSTP_instance(graph& input_graph, std::vector<int>& leaf_terminal, double M) {


	int N = num_vertices(input_graph);
	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	typedef graph::edge_descriptor Edge;
	pair<Edge, bool> ed;

	for (int i = 0; i < N; i++) {
		if (leaf_terminal[i] == 1) {
			boost::put(boost::vertex_name_t(), input_graph, 
				i, get(boost::vertex_name_t(), input_graph, i) + M); // change node weight
			boost::tie(ai, a_end) = boost::adjacent_vertices(i, input_graph);
			for (; ai != a_end; ai++) {
				int j = *ai;
				double cij = get(boost::edge_weight_t(), input_graph, boost::edge(i, j, input_graph).first);
				ed = boost::edge(i, j, input_graph);
				boost::put(boost::edge_weight_t(), input_graph, ed.first, cij + M); // update edge cost
			}
		}
	}
}
#pragma endregion transform_NWPFSTP_instance 



/*input and output*/

#pragma region  
graph read_NWPFSTP_data_with_leafterminals(string file_name, std::vector<int>& terminal, std::vector<int>& leaf_terminal) {

	int V_num; // vertex number
	int P_num; // number of positive vertices
	int E_num; // edge number
	int v1;
	int v2;
	double weight;
	graph input_graph; // define the adjacency list of the input graph; there is no need to define the V_num
	string line_content;
	ifstream myfile(file_name); // open the file
	if (myfile.is_open()) // if the file is opened successfully
	{
		while (getline(myfile, line_content)) // read file line by line
		{
			// parse the sting£ºline_content
			list<string> Parsed_content;
			std::string delimiter = " "; // the delimiter
			size_t pos = 0;
			std::string token;
			while ((pos = line_content.find(delimiter)) != std::string::npos) {
				// find(const string& str, size_t pos = 0) function returns the position of the first occurrence of str in the string, or npos if the string is not found.
				token = line_content.substr(0, pos);
				// The substr(size_t pos = 0, size_t n = npos) function returns a substring of the object, starting at position pos and of length npos
				Parsed_content.push_back(token); // store the subtr to the list
				line_content.erase(0, pos + delimiter.length()); // remove the front substr and the first delimiter
			}
			Parsed_content.push_back(line_content); // store the subtr to the list
			if (!Parsed_content.front().compare("Nodes")) // when it's equal, compare returns 0
			{
				Parsed_content.pop_front();
				V_num = atoi(Parsed_content.front().c_str()); // convert string to int
				terminal.resize(V_num);
				leaf_terminal.resize(V_num);
				for (int i = 0; i < V_num; i++) {
					boost::add_vertex(i, input_graph);
					boost::put(boost::vertex_name_t(), input_graph, i, 0);
				}
			}
			else if (!Parsed_content.front().compare("Edges"))
			{
				Parsed_content.pop_front();
				E_num = atoi(Parsed_content.front().c_str());
			}
			else if (!Parsed_content.front().compare("E"))
			{
				Parsed_content.pop_front(); // remove E, expose v1
				v1 = atoi(Parsed_content.front().c_str()) - 1;
				Parsed_content.pop_front(); // remove v1, expose v2
				v2 = atoi(Parsed_content.front().c_str()) - 1;
				Parsed_content.pop_front(); // remove v2, expose weight
				weight = stod(Parsed_content.front().c_str());
				boost::add_edge(v1, v2, weight, input_graph); // add edge
			}
			else if (!Parsed_content.front().compare("Terminals"))
			{
				Parsed_content.pop_front();
				P_num = atoi(Parsed_content.front().c_str());
			}
			else if (!Parsed_content.front().compare("TP"))
			{
				Parsed_content.pop_front(); // remove TP, expose v1
				v1 = atoi(Parsed_content.front().c_str()) - 1;
				Parsed_content.pop_front(); // remove v1, expose weight
				boost::put(boost::vertex_name_t(), input_graph, v1, stof(Parsed_content.front().c_str()));
			}
			else if (!Parsed_content.front().compare("CTP"))
			{
				Parsed_content.pop_front(); // remove CTP, expose v1
				v1 = atoi(Parsed_content.front().c_str()) - 1;
				boost::put(boost::vertex_name_t(), input_graph, v1, 0);  // give terminals big prize
				terminal[v1] = 1;
			}
			else if (!Parsed_content.front().compare("LCTP"))
			{
				Parsed_content.pop_front(); // remove CTP, expose v1
				v1 = atoi(Parsed_content.front().c_str()) - 1;
				leaf_terminal[v1] = 1;
			}
		}

		// check number of vertices
		std::cout << "|V|= " << num_vertices(input_graph);
		//std::cout << "  |P|= " << P_num;
		// check number of edges
		std::cout << "  |E|= " << num_edges(input_graph);
		// print errors
		if (V_num != num_vertices(input_graph)) {
			std::cout << "Error: the number of the input vertices is not right." << endl;
		}
		if (E_num != num_edges(input_graph)) {
			std::cout << "Error: the number of the input edges is not right." << endl;
		}
		// connectivity
		std::vector<int> component(num_vertices(input_graph)); // vertex i is in component[i]; No.component from 0
		int cpn_num = connected_components(input_graph, &component[0]); // the number of component; decrease component
		if (cpn_num > 1) {
			std::cout << "cpn_num: " << cpn_num << endl;
			std::cout << "Error: cpn_num>1" << endl;
		}
		return input_graph;

		myfile.close(); //close the file
	}
	else
	{
		std::cout << "Unable to open file " << file_name << endl << "Please check the file location or file name." << endl; // throw an error message
		getchar(); // keep the console window
		exit(1); // end the program
	}
}
#pragma endregion read_NWPFSTP_data_with_leafterminals 

#pragma region
void save_NWPFSTP_graph_with_leafterminals(string instance_name, graph& result_graph,
	std::vector<int>& terminal, std::vector<int>& leaf_terminal) {

	string save_name = instance_name; // save_name
	ofstream outputFile;
	outputFile.precision(20);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open(save_name + ".stp"); // stp file

	outputFile << "33D32945 STP File, STP Format Version 1.0" << endl;
	outputFile << endl;

	// comments
	outputFile << "SECTION Comments" << endl;
	outputFile << "Name \"" << save_name << "\"" << endl;
	outputFile << "Creator \"Yahui Sun\"" << endl;
	outputFile << "Problem \"Node - Weighted Steiner Problem in Graphs\"" << endl;
	outputFile << "END" << endl;
	outputFile << endl;

	// graph
	outputFile << "SECTION Graph" << endl;
	outputFile << "Nodes " << num_vertices(result_graph) << endl;
	outputFile << "Edges " << num_edges(result_graph) << endl;
	graph::out_edge_iterator eit, eend;
	for (int i = 0; i < num_vertices(result_graph); i++) {
		tie(eit, eend) = boost::out_edges(i, result_graph); // adjacent_vertices of 2
		for_each(eit, eend,
			[&result_graph, &i, &outputFile](graph::edge_descriptor it)
		{
			int j = boost::target(it, result_graph);
			if (i < j) {
				outputFile << "E " << i + 1 << " " << j + 1 << " " << get(boost::edge_weight_t(), result_graph, boost::edge(i, j, result_graph).first) << endl;
			}
		});
	}
	outputFile << "END" << endl;
	outputFile << endl;

	// TP
	outputFile << "SECTION Node Weights" << endl;
	for (int i = 0; i < num_vertices(result_graph); i++) {
		outputFile << "TP " << i + 1 << " " << get(boost::vertex_name_t(), result_graph, i) << endl;
	}
	outputFile << "END" << endl;
	outputFile << endl;

	// CTP
	outputFile << "SECTION Compulsory Terminals" << endl;
	for (int i = 0; i < num_vertices(result_graph); i++) {
		if (terminal[i] == 1) {
			outputFile << "CTP " << i + 1 << endl;
		}
	}
	outputFile << "END" << endl;
	outputFile << endl;

	// LCTP
	outputFile << "SECTION Leaf Compulsory Terminals" << endl;
	for (int i = 0; i < num_vertices(result_graph); i++) {
		if (leaf_terminal[i] == 1) {
			outputFile << "LCTP " << i + 1 << endl;
		}
	}
	outputFile << "END" << endl;
	outputFile << endl;


	outputFile << "EOF" << endl;

}
#pragma endregion save_NWPFSTP_graph_with_leafterminals  

#pragma region
void save_NWPFSTP_graph_with_leafterminals_Daniel(string instance_name, graph result_graph, std::vector<int> terminal, std::vector<int> leaf_terminal) {

	string save_name = instance_name; // save_name
	ofstream outputFile;
	outputFile.precision(20);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open(save_name + ".stp"); // stp file

	outputFile << "33D32945 STP File, STP Format Version 1.0" << endl;
	outputFile << endl;

	// comments
	outputFile << "SECTION Comments" << endl;
	outputFile << "Name \"" << save_name << "\"" << endl;
	outputFile << "Creator \"Yahui Sun\"" << endl;
	outputFile << "Problem \"Node - Weighted Steiner Problem in Graphs\"" << endl;
	outputFile << "END" << endl;
	outputFile << endl;

	// graph
	outputFile << "SECTION Graph" << endl;
	outputFile << "Nodes " << num_vertices(result_graph) << endl;
	outputFile << "Edges " << num_edges(result_graph) << endl;
	graph::out_edge_iterator eit, eend;
	for (int i = 0; i < num_vertices(result_graph); i++) {
		tie(eit, eend) = boost::out_edges(i, result_graph); // adjacent_vertices of 2
		for_each(eit, eend,
			[&result_graph, &i, &outputFile](graph::edge_descriptor it)
		{
			int j = boost::target(it, result_graph);
			if (i < j) {
				outputFile << "E " << i + 1 << " " << j + 1 << " " << get(boost::edge_weight_t(), result_graph, boost::edge(i, j, result_graph).first) << endl;
			}
		});
	}
	outputFile << "END" << endl;
	outputFile << endl;



	// CTP
	outputFile << "SECTION Terminals" << endl;
	for (int i = 0; i < num_vertices(result_graph); i++) {
		if (terminal[i] == 1) {
			if (leaf_terminal[i] == 1) {
				outputFile << "TL " << i + 1 << endl;
			}
			else {
				outputFile << "T " << i + 1 << endl;
			}

		}
	}
	outputFile << "END" << endl;
	outputFile << endl;

	// TP
	outputFile << "SECTION NodeWeights" << endl;
	for (int i = 0; i < num_vertices(result_graph); i++) {
		outputFile << "NW " << get(boost::vertex_name_t(), result_graph, i) << endl;
	}
	outputFile << "END" << endl;
	outputFile << endl;



	outputFile << "EOF" << endl;

}
#pragma endregion save_NWPFSTP_graph_with_leafterminals_Daniel 




/*PSTA*/

#pragma region 
std::vector<pair<int, int>> boost_graph_find_MST_fastMST(graph& input_graph) {

	std::vector<pair<int, int>> MST_edges;
	pair<int, int> new_edge;

	int N = num_vertices(input_graph);
	std::vector <boost::graph_traits<graph>::vertex_descriptor> p(N); // minimum_spanning_tree traits

	if (in_degree(0, input_graph) > 0) { // 0 is connected
		// find minimum_spanning_tree
		prim_minimum_spanning_tree(input_graph, &p[0]); // it can only be &p[0], and 0 must be connected in MST;
		// print edges in minimum_spanning_tree
		for (int i = 1; i != p.size(); ++i) { // p[0]=0;
			if (p[i] != i) {
				new_edge = { i, p[i] };
				MST_edges.insert(MST_edges.end(), new_edge);
			}
		}
	}
	else { // 0 is disconnected
		int v1 = 0;
		for (int i = 1; i < N; i++) {
			if (in_degree(i, input_graph) > 0) {
				v1 = i;
				break;
			}
		}
		boost::add_edge(0, v1, 1, input_graph); // add edge (0,v1)
		// find minimum_spanning_tree
		prim_minimum_spanning_tree(input_graph, &p[0]); // it can only be &p[0]; if 0 is disconnected, you need a fake edge to connect it
		for (int i = 1; i != p.size(); ++i) { // p[0]=0;
			if (p[i] != i && p[i] != 0) { // do not add edge (0,v1)
				new_edge = { i, p[i] };
				MST_edges.insert(MST_edges.end(), new_edge);
			}
		}
		boost::remove_edge(0, v1, input_graph); // remove edge (0,v1)
	}

	return MST_edges;
}
#pragma endregion boost_graph_find_MST_fastMST  

#pragma region
double net_cost_KleinNWSTP_fastMST(graph& input_graph, std::vector<pair<int, int>>& MST_edges, std::vector<int>& terminal) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;

	double included_cost = 0;
	int N = num_vertices(input_graph); // number of vertices

	std::vector<bool> vertex_included(N);
	for (int i = 0; i < MST_edges.size(); i++) {
		vertex_included[MST_edges[i].first] = true;
		vertex_included[MST_edges[i].second] = true;
		included_cost = included_cost +
			get(boost::edge_weight_t(), input_graph, boost::edge(MST_edges[i].first, MST_edges[i].second, input_graph).first);// included ec
	}


	for (int i = 0; i < N; i++) {
		if (vertex_included[i] == true && terminal[i] == 0) {
			included_cost = included_cost + get(boost::vertex_name_t(), input_graph, i); // included nw
		}
	}

	return included_cost;
}
#pragma endregion net_cost_KleinNWSTP_fastMST

#pragma region
std::vector<pair<int, int>> pressure_as_cost_with_nw_find_MST_NWPTSTP_fastMST
(graph& original_transformed_input_graph, graph& input_graph, std::vector<pair<int, int>>& MST_edges,
	std::vector<double>& pressure, std::vector<int>& terminal, std::vector<int>& leaf_terminal) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	typedef graph::edge_descriptor Edge;
	int N = num_vertices(input_graph);
	int E = num_edges(input_graph);

	int calculated_flux_num = 0;
	for (int i = 0; i < N; i++) {
		boost::tie(ai, a_end) = boost::adjacent_vertices(i, original_transformed_input_graph);
		for (; ai != a_end; ai++) {
			int  j = *ai;
			if (i < j) { // don't add the same edge twice
				double new_C = get(boost::edge_weight_t(), original_transformed_input_graph, 
					boost::edge(i, j, original_transformed_input_graph).first);
				if (terminal[i] == 0) {
					new_C = new_C + get(boost::vertex_name_t(), original_transformed_input_graph, i);
				}
				if (terminal[j] == 0) {
					new_C = new_C + get(boost::vertex_name_t(), original_transformed_input_graph, j);
				}
				double flux = (pressure[i] - pressure[j]) / new_C;
				flux = abs(flux); // absolute value
				calculated_flux_num++;
				//cout << flux << endl;
				pair<Edge, bool> ed = boost::edge(i, j, input_graph);
				double new_edge_cost = pow((1 / flux), 1); // new edge cost 
				boost::put(boost::edge_weight_t(), input_graph, ed.first, new_edge_cost); // update edge costs
			}
		}
	}

	for (int i = 0; i < N; i++) {
		boost::tie(ai, a_end) = boost::adjacent_vertices(i, input_graph);
		for (; ai != a_end; ai++) {
			if (*ai > i) {
				double ec = get(boost::edge_weight_t(), input_graph, boost::edge(i, *ai, input_graph).first);
				if (isnan(ec)) {
					pair<Edge, bool> ed = boost::edge(i, *ai, input_graph);
					boost::put(boost::edge_weight_t(), input_graph, ed.first, 0); // change NaN to 0; flux is nan: 0/0 (bs ec=0)
				}
				if (isinf(ec)) {
					pair<Edge, bool> ed = boost::edge(i, *ai, input_graph);
					boost::put(boost::edge_weight_t(), input_graph, ed.first, 1e20); // change Inf to 1e20; otherwise MST is not a spanning tree
				}
			}
		}

	}


	double total_ec_and_nw = boost_graph_sum_of_nw_and_ec(input_graph, num_vertices(input_graph));
	transform_NWPFSTP_instance(input_graph, leaf_terminal, 10 * total_ec_and_nw); // transform ec
	std::vector<pair<int, int>> newMST_edges = boost_graph_find_MST_fastMST(input_graph);

	boost_graph_transform_ec_nw_back(original_transformed_input_graph, input_graph);


	return newMST_edges;

}
#pragma endregion pressure_as_cost_with_nw_find_MST_NWPTSTP_fastMST

#pragma region
std::vector<pair<int, int>> remove_noncompulsory_leaves_fastMST
(int N, std::vector<pair<int, int>>& graph_edges, std::vector<int>& terminal) {


	//cout << graph_edges.size() << endl;

	pair<int, int> new_edge;
	std::vector<std::vector<pair<int, int>>> Vertex_adj_edges(N);
	for (int i = 0; i < graph_edges.size(); i++) {
		new_edge = { graph_edges[i].first,graph_edges[i].second };
		Vertex_adj_edges[graph_edges[i].first].insert(Vertex_adj_edges[graph_edges[i].first].end(), new_edge);
		new_edge = { graph_edges[i].second,graph_edges[i].first };
		Vertex_adj_edges[graph_edges[i].second].insert(Vertex_adj_edges[graph_edges[i].second].end(), new_edge);
	}

	std::vector<int> noncompulsory_leaves;
	for (int i = 0; i < N; i++) {
		if (Vertex_adj_edges[i].size() == 1 && terminal[i] == 0) {
			noncompulsory_leaves.insert(noncompulsory_leaves.end(), i);
		}
	}

	while (noncompulsory_leaves.size() > 0) {

		int e1 = noncompulsory_leaves[0];
		//cout << Vertex_adj_edges[noncompulsory_leaves[0]].size() << endl;
		int e2 = Vertex_adj_edges[e1][0].second;

		// remove edges
		noncompulsory_leaves.erase(noncompulsory_leaves.begin());
		//cout << "remove edge " << e1 << "," << e2 << endl;
		Vertex_adj_edges[e1].clear();
		for (int i = 0; i < Vertex_adj_edges[e2].size(); i++) {
			if (Vertex_adj_edges[e2][i].second == e1) {
				//cout << "remove edge " << e2 << "," << e1 << endl;
				Vertex_adj_edges[e2].erase(Vertex_adj_edges[e2].begin() + i);
				if (Vertex_adj_edges[e2].size() == 1 && terminal[e2] == 0) {
					noncompulsory_leaves.insert(noncompulsory_leaves.end(), e2);
				}
				break;
			}
		}

	}

	graph_edges.clear();// output edges
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < Vertex_adj_edges[i].size(); j++) {
			int e1 = Vertex_adj_edges[i][j].first;
			int e2 = Vertex_adj_edges[i][j].second;
			if (e1 < e2) {
				new_edge = { e1,e2 };
				graph_edges.insert(graph_edges.end(), new_edge);
			}
		}
	}

	return graph_edges;
}
#pragma endregion remove_noncompulsory_leaves_fastMST

#pragma region 
std::vector<pair<int, int>> boost_graph_MST_postprocessing_fastMST
(graph& original_transformed_input_graph, graph& input_graph, std::vector<pair<int, int>>& graph_edges) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	typedef graph::edge_descriptor Edge;

	int N = num_vertices(input_graph);
	std::vector<bool> vertex_included(N);
	for (int i = 0; i < graph_edges.size(); i++) {
		int e1 = graph_edges[i].first;
		int e2 = graph_edges[i].second;
		vertex_included[e1] = true;
		vertex_included[e2] = true;
	}

	double M = 1e100;
	for (int i = 0; i < N; i++) {
		if (vertex_included[i] == false) { // i is not in solu_graph
			boost::tie(ai, a_end) = boost::adjacent_vertices(i, input_graph);
			for (; ai != a_end; ai++) {
				int j = *ai;
				pair<Edge, bool> ed = boost::edge(i, j, input_graph);
				boost::put(boost::edge_weight_t(), input_graph, ed.first, M);
			}
		}
	}

	std::vector<pair<int, int>> MST_edges = boost_graph_find_MST_fastMST(input_graph);

	for (int i = 0; i < MST_edges.size(); i++) {
		if (vertex_included[MST_edges[i].first] == false || vertex_included[MST_edges[i].second] == false) {
			MST_edges.erase(MST_edges.begin() + i); // remove edges not in the subgraph
			i--;
		}
	}

	boost_graph_transform_ec_nw_back(original_transformed_input_graph, input_graph);

	return MST_edges;
}

#pragma endregion boost_graph_MST_postprocessing_fastMST  

#pragma region
std::vector<pair<int, int>> copy_edge_vectors(std::vector<pair<int, int>>& edges) {

	return edges;
}
#pragma endregion copy_edge_vectors

#pragma region
graph PSTA_NWPTSTP_CCG_fastMST(graph input_graph, std::vector<int> terminal, std::vector<int> leaf_terminal,
	int K, int& best_solution_K) {

	graph original_graph = copy_graph(input_graph);

	/*transform_NWPFSTP_instance*/
	int N = num_vertices(input_graph);
	double total_ec_and_nw = boost_graph_sum_of_nw_and_ec(input_graph, num_vertices(input_graph));
	transform_NWPFSTP_instance(input_graph, leaf_terminal, total_ec_and_nw); // transform ec
	graph original_transformed_input_graph = copy_graph(input_graph);

	/*initialize best solution*/
	std::vector<pair<int, int>> best_spanningtree_edges = boost_graph_find_MST_fastMST(input_graph);
	double best_spanning_cost = net_cost_KleinNWSTP_fastMST(input_graph, best_spanningtree_edges, terminal);

	/*iteration*/
	double new_spanning_cost;
	for (int iteration_times = 0; iteration_times < K; iteration_times++) {

		/*random pressures*/
		std::vector<double> pressure;
		for (int i = 0; i < N; i++) {
			pressure.insert(pressure.end(), 1e4 - rand() % (int) 2e4);  // give vertices random pressures
		}

		/*calculated MST for updated edge costs*/
		std::vector<pair<int, int>> evolution_graph_edges = pressure_as_cost_with_nw_find_MST_NWPTSTP_fastMST
		(original_transformed_input_graph, input_graph, best_spanningtree_edges, pressure, terminal, leaf_terminal);

		/*remove_noncompulsory_leaves*/
		evolution_graph_edges = remove_noncompulsory_leaves_fastMST(N, evolution_graph_edges, terminal);

		/*calculated MST for transformed edge costs*/
		evolution_graph_edges = boost_graph_MST_postprocessing_fastMST(original_transformed_input_graph, input_graph, evolution_graph_edges);

		/*remove_noncompulsory_leaves*/
		evolution_graph_edges = remove_noncompulsory_leaves_fastMST(N, evolution_graph_edges, terminal);


		new_spanning_cost = net_cost_KleinNWSTP_fastMST(input_graph, evolution_graph_edges, terminal);
		if (new_spanning_cost < best_spanning_cost) {
			best_solution_K = iteration_times + 1;
			best_spanning_cost = new_spanning_cost;
			best_spanningtree_edges = copy_edge_vectors(evolution_graph_edges); // update best_spanningtree
		}

	}


	graph best_spanningtree(N);
	for (int i = 0; i < best_spanningtree_edges.size(); i++) {
		int e1 = best_spanningtree_edges[i].first;
		int e2 = best_spanningtree_edges[i].second;
		boost::add_edge(e1, e2, 1, best_spanningtree);
	}
	boost_graph_transform_ec_nw_back(original_graph, best_spanningtree);

	return best_spanningtree;


}
#pragma endregion PSTA_NWPTSTP_CCG_fastMST



/*Guha_16103*/

#pragma region 
bool compare_tree_distance(const pair<int, double>&i, const pair<int, double>&j)
{
	return i.second < j.second;  // < is from small to big; > is from big to small.  sort by the second item of pair<int, int>
}

bool compare_path_distance(const pair<pair<pair<int, int>, pair<int, int>>, double>&i, const pair<pair<pair<int, int>, pair<int, int>>, double>&j)
{
	return i.second < j.second;  // < is from small to big; > is from big to small.  sort by the second item of pair<int, int>
}


void contract_trees(std::vector<pair<int, int>>& contracted_edges, std::vector<int>& contracted_non_terminals,
	std::vector<int> contracted_tree_IDs, std::vector<std::vector<int>>& terminal_trees, std::vector<int>& vertex_is_in_terminal_trees,
	graph& g2, graph& solution_graph) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	typedef graph::edge_descriptor Edge;

	int new_tree_ID = contracted_tree_IDs[0];
	for (int y = 1; y < contracted_tree_IDs.size(); y++) {
		int contracted_tree_ID = contracted_tree_IDs[y];
		for (int x = 0; x < terminal_trees[contracted_tree_ID].size(); x++) {
			terminal_trees[new_tree_ID].insert(terminal_trees[new_tree_ID].end(),
				terminal_trees[contracted_tree_ID][x]); // move contracted_tree to new_tree
		}
		terminal_trees.erase(terminal_trees.begin() + contracted_tree_ID); // erase contracted_tree
		for (int z = y; z < contracted_tree_IDs.size(); z++) {
			if (contracted_tree_IDs[z] > contracted_tree_ID) {
				contracted_tree_IDs[z]--; // update tree_ID
			}
		}
		if (new_tree_ID > contracted_tree_ID) { // correct version
			new_tree_ID--;
		}
	}
	for (int x = 0; x < contracted_non_terminals.size(); x++) {
		terminal_trees[new_tree_ID].insert(terminal_trees[new_tree_ID].end(),
			contracted_non_terminals[x]); // move contracted_non_terminals to new_tree
		double old_nw = get(boost::vertex_name_t(), g2, contracted_non_terminals[x]);
		boost::tie(ai, a_end) = boost::adjacent_vertices(contracted_non_terminals[x], g2);
		for (; ai != a_end; ai++) {
			pair<Edge, bool> ed = boost::edge(contracted_non_terminals[x], *ai, g2);
			double old_ec = get(boost::edge_weight_t(), g2, boost::edge(contracted_non_terminals[x], *ai, g2).first);
			boost::put(boost::edge_weight_t(), g2, ed.first, old_ec - old_nw / 2); // update adj ec of contracted_non_terminals[x]
		}
		boost::put(boost::vertex_name_t(), g2, contracted_non_terminals[x], 0); // update nw of contracted_non_terminals[x]
	}
	for (int x = 0; x < contracted_edges.size(); x++) {
		pair<Edge, bool> ed = boost::edge(contracted_edges[x].first, contracted_edges[x].second, solution_graph);
		//cout << "checking contracted_edge:(" << contracted_edges[x].first << "," << contracted_edges[x].second << ")" << endl;
		if (!ed.second) { // this edge does not exist in solution_graph
						  //cout << "contracted_edge:(" << contracted_edges[x].first << "," << contracted_edges[x].second << ")" << endl;
			boost::add_edge(contracted_edges[x].first, contracted_edges[x].second, 1, solution_graph); // put new edge into solution_graph
			ed = boost::edge(contracted_edges[x].first, contracted_edges[x].second, g2);
			boost::put(boost::edge_weight_t(), g2, ed.first, 0); // update ec of new edge
		}
	}

}


void contract_minimum_ratio_spider(int N, double total_ec_and_nw, int terminal_trees_num,
	int minimum_ratio_start_v, int minimum_ratio_spidering_tree_num,
	std::vector<std::vector<int>>& terminal_trees, std::vector<int>& vertex_is_in_terminal_trees,
	graph& g2, graph& solution_graph) {

	typedef graph::edge_descriptor Edge;


	// Create things for Dijkstra
	std::vector<int> predecessors(N); // To store parents
	std::vector<double> distances(N); // To store distances
	typedef boost::property_map < graph, boost::vertex_index_t >::type IndexMap;
	IndexMap indexMap = boost::get(boost::vertex_index, g2);
	typedef boost::iterator_property_map < int*, IndexMap, int, int& > PredecessorMap;
	PredecessorMap predecessorMap(&predecessors[0], indexMap);
	typedef boost::iterator_property_map < double*, IndexMap, double, double& > DistanceMap;
	DistanceMap distanceMap(&distances[0], indexMap);
	boost::dijkstra_shortest_paths(g2, minimum_ratio_start_v,
		boost::distance_map(distanceMap).predecessor_map(predecessorMap)); // all SPs to minimum_ratio_start_v

	std::vector<pair<int, double>> distances_queue; // item: <tree_ID, distances_from_start_v_to_terminal_trees[tree_ID]>
	std::vector<double> distances_from_start_v_to_terminal_trees(terminal_trees_num); // LP distances_from_start_v_to_terminal_trees
	for (int tree_ID = 0; tree_ID < terminal_trees_num; tree_ID++) {
		distances_from_start_v_to_terminal_trees[tree_ID] = 1e2* total_ec_and_nw;
		for (int x = 0; x < terminal_trees[tree_ID].size(); x++) {

			double distance_v_to_x = distanceMap[terminal_trees[tree_ID][x]];
			if (distance_v_to_x != 0) { // if distance_v_to_x==0, then v == x, distance_v_to_x = 0
				distance_v_to_x = distance_v_to_x - get(boost::vertex_name_t(), g2, minimum_ratio_start_v) / 2; // remove nw/2 of v; vertices in trees have 0 nw
			}

			if (distance_v_to_x < distances_from_start_v_to_terminal_trees[tree_ID]) {
				distances_from_start_v_to_terminal_trees[tree_ID] = distance_v_to_x; // distance from v to x in this tree
			}
		}
		pair<int, double> queue_item = { tree_ID, distances_from_start_v_to_terminal_trees[tree_ID] };
		distances_queue.insert(distances_queue.end(), queue_item);
	}

	sort(distances_queue.begin(), distances_queue.end(), compare_tree_distance); // sort from small to large

																				 //for (int a = 0; a < distances_queue.size(); a++) {
																				 //	cout << distances_queue[a].first << " " << distances_queue[a].second << endl;
																				 //}

																				 // contract minimum_ratio_spidering_tree_num trees in distances_queue
	std::vector<pair<int, int>> contracted_edges;
	std::vector<int> contracted_non_terminals;
	std::vector<int> contracted_tree_IDs;
	for (int y = 0; y < minimum_ratio_spidering_tree_num; y++) { // contract minimum_ratio_spidering_tree_num trees in distances_queue
		int contracted_tree_ID = distances_queue[y].first;
		double mini_distances = 1e2* total_ec_and_nw;
		int contracted_x;
		for (int x = 0; x < terminal_trees[contracted_tree_ID].size(); x++) {
			//cout << "terminal_trees[contracted_tree_ID][x]:" << terminal_trees[contracted_tree_ID][x] << endl;
			double distance_v_to_x = distanceMap[terminal_trees[contracted_tree_ID][x]];
			if (distance_v_to_x < mini_distances) {
				mini_distances = distance_v_to_x; // distance from v to x in this tree
				contracted_x = terminal_trees[contracted_tree_ID][x];
			}
		}
		int v = contracted_x; // destionation
							  //cout << "SP from " << minimum_ratio_start_v << " to " << contracted_x << endl;
		for (int u = predecessorMap[v]; // Start by setting 'u' to the destintaion node's predecessor
			u != v; // Keep tracking the path until we get to the source
			v = u, u = predecessorMap[v]) // Set the current vertex to the current predecessor, and the predecessor to one level up
		{
			//cout << "checking insert contracted_edge:(" << u << "," << v << ")" << endl;
			pair<Edge, bool> ed = boost::edge(v, u, solution_graph);
			if (!ed.second) { // this edge does not exist in solution_graph
				pair<int, int> new_edge = { u,v };
				//cout << "insert contracted_edge:(" << u << "," << v << ")" << endl;
				contracted_edges.insert(contracted_edges.end(), new_edge);
				if (vertex_is_in_terminal_trees[u] == 0) {
					contracted_non_terminals.insert(contracted_non_terminals.end(), u);
					vertex_is_in_terminal_trees[u] = 1;
				}
			}
		}
	}
	for (int y = 0; y < minimum_ratio_spidering_tree_num; y++) {
		contracted_tree_IDs.insert(contracted_tree_IDs.end(), distances_queue[y].first);
	}
	contract_trees(contracted_edges, contracted_non_terminals, contracted_tree_IDs, terminal_trees,
		vertex_is_in_terminal_trees, g2, solution_graph); // contract_trees



}



graph Guha_16103(graph instance_graph, std::vector<int> terminal, std::vector<int> leaf_terminal) {

	graph::out_edge_iterator eit, eend;
	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	typedef graph::edge_descriptor Edge;

	int N = num_vertices(instance_graph);

	for (int i = 0; i < N; i++) {
		if (terminal[i] == 0) { // i is relay with nw
		}
		else {
			boost::put(boost::vertex_name_t(), instance_graph, i, 0); // terminal has 0 nw
		}
	}


	// increase sensor-relay ec
	double total_ec_and_nw = boost_graph_sum_of_nw_and_ec(instance_graph, num_vertices(instance_graph));
	graph transformed_instance_graph = copy_graph(instance_graph);
	transform_NWPFSTP_instance(transformed_instance_graph, leaf_terminal, total_ec_and_nw);


	graph solution_graph(N); // no edge inside initially


	graph g2 = copy_graph(transformed_instance_graph); // nw has been embeded onto edges in g2
	for (int i = 0; i < N; i++) {
		if (terminal[i] == 0) { // i is relay with nw
			double original_nw = get(boost::vertex_name_t(), g2, i);
			boost::tie(ai, a_end) = boost::adjacent_vertices(i, g2);
			for (; ai != a_end; ai++) { // adjacent vertices of i
				double original_ec = get(boost::edge_weight_t(), g2, boost::edge(i, *ai, g2).first);
				boost::put(boost::edge_weight_t(), g2, boost::edge(i, *ai, g2).first, original_ec + original_nw / 2); // distribute relay costs onto edges
			}
		}
		else {
			boost::put(boost::vertex_name_t(), g2, i, 0); // terminal has 0 nw
		}
	}


	std::vector<std::vector<int>> terminal_trees;
	for (int i = 0; i < N; i++) {
		if (terminal[i] == 1) {
			std::vector<int> tree = { i };
			terminal_trees.insert(terminal_trees.end(), tree); // each terminal is a terminal_tree initially
		}
	}

	std::vector<int> vertex_is_in_terminal_trees = copy_vector_int(terminal);


	while (terminal_trees.size() > 2) { // if there are only two terminal trees left, then connect them optimally


		int terminal_trees_num = terminal_trees.size();

		//cout << "terminal_trees.size():" << terminal_trees.size() << endl;


		double minimum_ratio = 1e2* total_ec_and_nw, minimum_ratio_three_plus_spider = 1e2* total_ec_and_nw;
		int minimum_ratio_start_v, minimum_ratio_three_plus_spider_start_v;
		int minimum_ratio_spidering_tree_num, minimum_ratio_three_plus_spider_spidering_tree_num;

		// find a spider wih the minimum ratio
		for (int start_v = 0; start_v < N; start_v++) {

			// Create things for Dijkstra
			std::vector<int> predecessors(N); // To store parents
			std::vector<double> distances(N); // To store distances
			typedef boost::property_map < graph, boost::vertex_index_t >::type IndexMap;
			IndexMap indexMap = boost::get(boost::vertex_index, g2);
			typedef boost::iterator_property_map < int*, IndexMap, int, int& > PredecessorMap;
			PredecessorMap predecessorMap(&predecessors[0], indexMap);
			typedef boost::iterator_property_map < double*, IndexMap, double, double& > DistanceMap;
			DistanceMap distanceMap(&distances[0], indexMap);
			boost::dijkstra_shortest_paths(g2, start_v,
				boost::distance_map(distanceMap).predecessor_map(predecessorMap)); // all SPs to start_v

			std::vector<pair<int, double>> distances_queue; // item: <tree_ID, distances_from_start_v_to_terminal_trees[tree_ID]>
			std::vector<double> distances_from_start_v_to_terminal_trees(terminal_trees_num); // LP distances_from_start_v_to_terminal_trees
			for (int tree_ID = 0; tree_ID < terminal_trees_num; tree_ID++) {
				distances_from_start_v_to_terminal_trees[tree_ID] = 1e2* total_ec_and_nw;
				for (int x = 0; x < terminal_trees[tree_ID].size(); x++) {

					double distance_v_to_x = distanceMap[terminal_trees[tree_ID][x]];
					if (distance_v_to_x != 0) { // if distance_v_to_x==0, then v == x, distance_v_to_x = 0
						distance_v_to_x = distance_v_to_x - get(boost::vertex_name_t(), g2, start_v) / 2; // remove nw/2 of v; vertices in trees have 0 nw
					}

					if (distance_v_to_x < distances_from_start_v_to_terminal_trees[tree_ID]) {
						distances_from_start_v_to_terminal_trees[tree_ID] = distance_v_to_x; // distance from v to x in this tree
					}
				}
				pair<int, double> queue_item = { tree_ID, distances_from_start_v_to_terminal_trees[tree_ID] };
				distances_queue.insert(distances_queue.end(), queue_item);
			}

			sort(distances_queue.begin(), distances_queue.end(), compare_tree_distance); // sort from small to large

			double minimum_ratio_for_v = (get(boost::vertex_name_t(), g2, start_v) +
				distances_queue[0].second + distances_queue[1].second) / 2;
			double minimum_ratio_three_plus_spider_for_v;
			int minimum_ratio_for_v_spidering_tree_num = 2, minimum_ratio_three_plus_spider_for_v_spidering_tree_num;
			for (int y = 2; y < terminal_trees_num; y++) { // terminal_trees_num >2
				double ratio = get(boost::vertex_name_t(), g2, start_v);
				for (int x = 0; x <= y; x++) {
					ratio = ratio + distances_queue[x].second;
				}
				ratio = ratio / (y + 1);
				if (ratio < minimum_ratio_for_v) {
					minimum_ratio_for_v = ratio;
					minimum_ratio_for_v_spidering_tree_num = y + 1;
					minimum_ratio_three_plus_spider_for_v = ratio;
					minimum_ratio_three_plus_spider_for_v_spidering_tree_num = y + 1;
				}
				else {
					minimum_ratio_three_plus_spider_for_v = ratio;
					minimum_ratio_three_plus_spider_for_v_spidering_tree_num = y + 1;
					break;
				}
			}

			if (minimum_ratio > minimum_ratio_for_v) {
				minimum_ratio = minimum_ratio_for_v;
				minimum_ratio_start_v = start_v;
				minimum_ratio_spidering_tree_num = minimum_ratio_for_v_spidering_tree_num;
			}

			if (minimum_ratio_three_plus_spider > minimum_ratio_three_plus_spider_for_v) {
				minimum_ratio_three_plus_spider = minimum_ratio_three_plus_spider_for_v;
				minimum_ratio_three_plus_spider_start_v = start_v;
				minimum_ratio_three_plus_spider_spidering_tree_num = minimum_ratio_three_plus_spider_for_v_spidering_tree_num;
			}


		}


		//cout << "minimum_ratio_spidering_tree_num"<< minimum_ratio_spidering_tree_num << endl;


		if (minimum_ratio_spidering_tree_num >= 3) { // contract a 3+ spider: minimum_ratio_spidering_tree_num

			contract_minimum_ratio_spider(N, total_ec_and_nw, terminal_trees_num,
				minimum_ratio_start_v, minimum_ratio_spidering_tree_num,
				terminal_trees, vertex_is_in_terminal_trees, g2, solution_graph);

		}
		else {

			double value1;
			double value2 = 2 * terminal_trees_num*minimum_ratio;
			double value3 = 3 / 2 * terminal_trees_num*minimum_ratio_three_plus_spider;

			std::vector<pair<pair<pair<int, int>, pair<int, int>>, double>> Pj; // <<<tree_ID1,tree_ID2>,v1,v2>,distance>; tree_ID1< tree_ID2
			for (int x = 0; x < terminal_trees.size(); x++) {
				double min_distance = 1e2* total_ec_and_nw;
				int min_tree_ID, v1, v2;
				for (int y = 0; y < terminal_trees.size(); y++) {
					if (x != y) {
						// calculate distance from terminal_trees[x] to terminal_trees[y]
						for (int i = 0; i < terminal_trees[x].size(); i++) {
							// Create things for Dijkstra
							std::vector<int> predecessors(N); // To store parents
							std::vector<double> distances(N); // To store distances
							typedef boost::property_map < graph, boost::vertex_index_t >::type IndexMap;
							IndexMap indexMap = boost::get(boost::vertex_index, g2);
							typedef boost::iterator_property_map < int*, IndexMap, int, int& > PredecessorMap;
							PredecessorMap predecessorMap(&predecessors[0], indexMap);
							typedef boost::iterator_property_map < double*, IndexMap, double, double& > DistanceMap;
							DistanceMap distanceMap(&distances[0], indexMap);
							boost::dijkstra_shortest_paths(g2, terminal_trees[x][i],
								boost::distance_map(distanceMap).predecessor_map(predecessorMap)); // all SPs to terminal_trees[x][i]
							for (int k = 0; k < terminal_trees[y].size(); k++) {
								if (distanceMap[terminal_trees[y][k]] < min_distance) {
									min_distance = distanceMap[terminal_trees[y][k]];
									min_tree_ID = y;
									v1 = terminal_trees[x][i];
									v2 = terminal_trees[y][k];
								}
							}
						}
					}
				}
				bool identical = true;
				for (int i = 0; i < Pj.size(); i++) {
					if (Pj[i].first.first.first == x && Pj[i].first.first.second == min_tree_ID) {
						identical = false;
						break;
					}
					if (Pj[i].first.first.first == min_tree_ID && Pj[i].first.first.second == x) {
						identical = false;
						break;
					}
				}
				if (identical == true) { // 
					Pj.insert(Pj.end(), { { { x,min_tree_ID } ,{ v1, v2 } },min_distance }); // insert non identical path
				}
			}

			sort(Pj.begin(), Pj.end(), compare_path_distance); // sort from small to large

			int Li = 0;
			double costT = 0;
			for (int x = 0; x < Pj.size(); x++) {
				if (Pj[x].second <= 8 / 3 * minimum_ratio && Pj[x].second <= 2 * minimum_ratio_three_plus_spider) {
					Li++;
					costT = costT + Pj[x].second;
				}
				else {
					break;
				}
			}

			value1 = costT / (-log(1 - (double)Li / terminal_trees_num));


			if (isnan(value1)) { // this haappens when Li=0; costT=0; there is probably a bug here
				value1 = 1e2* total_ec_and_nw;
			}

			//cout << "costT:" << costT << " Li:" << Li << " terminal_trees_num:" << terminal_trees_num << endl;
			//cout << "value1:" << value1 << " value2:" << value2 << " value3:" << value3 << endl;


			if (value1 <= value2 && value1 <= value3) {

				std::vector<pair<int, int>> contracted_edges;
				std::vector<int> contracted_non_terminals;
				std::vector<int> contracted_tree_IDs;

				for (int x = 0; x < Li; x++) {

					int tree_ID1 = Pj[x].first.first.first;
					int new_tree_in_contracted_tree_IDs = true;
					for (int y = 0; y < contracted_tree_IDs.size(); y++) {
						if (contracted_tree_IDs[y] == tree_ID1) {
							new_tree_in_contracted_tree_IDs = false;
							break;
						}
					}
					if (new_tree_in_contracted_tree_IDs == true) {
						contracted_tree_IDs.insert(contracted_tree_IDs.end(), tree_ID1);
					}

					int tree_ID2 = Pj[x].first.first.second;
					new_tree_in_contracted_tree_IDs = true;
					for (int y = 0; y < contracted_tree_IDs.size(); y++) {
						if (contracted_tree_IDs[y] == tree_ID2) {
							new_tree_in_contracted_tree_IDs = false;
							break;
						}
					}
					if (new_tree_in_contracted_tree_IDs == true) {
						contracted_tree_IDs.insert(contracted_tree_IDs.end(), tree_ID2);
					}

					// Create things for Dijkstra
					std::vector<int> predecessors(N); // To store parents
					std::vector<double> distances(N); // To store distances
					typedef boost::property_map < graph, boost::vertex_index_t >::type IndexMap;
					IndexMap indexMap = boost::get(boost::vertex_index, g2);
					typedef boost::iterator_property_map < int*, IndexMap, int, int& > PredecessorMap;
					PredecessorMap predecessorMap(&predecessors[0], indexMap);
					typedef boost::iterator_property_map < double*, IndexMap, double, double& > DistanceMap;
					DistanceMap distanceMap(&distances[0], indexMap);
					boost::dijkstra_shortest_paths(g2, Pj[x].first.second.first,
						boost::distance_map(distanceMap).predecessor_map(predecessorMap)); // all SPs to Pj[x].first.second.first (v1)
					int v = Pj[x].first.second.second; // destionation v2
					for (int u = predecessorMap[v]; // Start by setting 'u' to the destintaion node's predecessor
						u != v; // Keep tracking the path until we get to the source
						v = u, u = predecessorMap[v]) // Set the current vertex to the current predecessor, and the predecessor to one level up
					{
						pair<Edge, bool> ed = boost::edge(v, u, solution_graph);
						if (!ed.second) { // this edge does not exist in solution_graph
							pair<int, int> new_edge = { u,v };
							contracted_edges.insert(contracted_edges.end(), new_edge);
							if (vertex_is_in_terminal_trees[u] == 0) {
								contracted_non_terminals.insert(contracted_non_terminals.end(), u);
								vertex_is_in_terminal_trees[u] = 1;
							}
						}
					}

				}

				contract_trees(contracted_edges, contracted_non_terminals, contracted_tree_IDs, terminal_trees,
					vertex_is_in_terminal_trees, g2, solution_graph); // contract_trees



			}
			else if (value2 <= value1 && value2 <= value3) {
				contract_minimum_ratio_spider(N, total_ec_and_nw, terminal_trees_num,
					minimum_ratio_start_v, minimum_ratio_spidering_tree_num,
					terminal_trees, vertex_is_in_terminal_trees, g2, solution_graph);
			}
			else if (value3 <= value1 && value3 <= value2) {
				contract_minimum_ratio_spider(N, total_ec_and_nw, terminal_trees_num,
					minimum_ratio_three_plus_spider_start_v, minimum_ratio_three_plus_spider_spidering_tree_num,
					terminal_trees, vertex_is_in_terminal_trees, g2, solution_graph);
			}

		}

		//getchar();

	}


	//cout << "terminal_trees.size():" << terminal_trees.size() << endl;


	if (terminal_trees.size() == 2) {

		std::vector<pair<int, int>> contracted_edges;
		std::vector<int> contracted_non_terminals;
		std::vector<int> contracted_tree_IDs = { 0 , 1 };

		double min_distance = 1e2* total_ec_and_nw;
		int v1, v2;
		// calculate distance from terminal_trees[0][i] to terminal_trees[1][k]
		for (int i = 0; i < terminal_trees[0].size(); i++) {
			// Create things for Dijkstra
			std::vector<int> predecessors(N); // To store parents
			std::vector<double> distances(N); // To store distances
			typedef boost::property_map < graph, boost::vertex_index_t >::type IndexMap;
			IndexMap indexMap = boost::get(boost::vertex_index, g2);
			typedef boost::iterator_property_map < int*, IndexMap, int, int& > PredecessorMap;
			PredecessorMap predecessorMap(&predecessors[0], indexMap);
			typedef boost::iterator_property_map < double*, IndexMap, double, double& > DistanceMap;
			DistanceMap distanceMap(&distances[0], indexMap);
			boost::dijkstra_shortest_paths(g2, terminal_trees[0][i],
				boost::distance_map(distanceMap).predecessor_map(predecessorMap)); // all SPs to terminal_trees[0][i]
			for (int k = 0; k < terminal_trees[1].size(); k++) {
				if (distanceMap[terminal_trees[1][k]] < min_distance) {
					min_distance = distanceMap[terminal_trees[1][k]];
					v1 = terminal_trees[0][i];
					v2 = terminal_trees[1][k];
				}
			}
		}


		// Create things for Dijkstra
		std::vector<int> predecessors(N); // To store parents
		std::vector<double> distances(N); // To store distances
		typedef boost::property_map < graph, boost::vertex_index_t >::type IndexMap;
		IndexMap indexMap = boost::get(boost::vertex_index, g2);
		typedef boost::iterator_property_map < int*, IndexMap, int, int& > PredecessorMap;
		PredecessorMap predecessorMap(&predecessors[0], indexMap);
		typedef boost::iterator_property_map < double*, IndexMap, double, double& > DistanceMap;
		DistanceMap distanceMap(&distances[0], indexMap);
		boost::dijkstra_shortest_paths(g2, v1,
			boost::distance_map(distanceMap).predecessor_map(predecessorMap)); // all SPs to (v1)
		int v = v2; // destionation v2
		for (int u = predecessorMap[v]; // Start by setting 'u' to the destintaion node's predecessor
			u != v; // Keep tracking the path until we get to the source
			v = u, u = predecessorMap[v]) // Set the current vertex to the current predecessor, and the predecessor to one level up
		{
			pair<Edge, bool> ed = boost::edge(v, u, solution_graph);
			if (!ed.second) { // this edge does not exist in solution_graph
				pair<int, int> new_edge = { u,v };
				contracted_edges.insert(contracted_edges.end(), new_edge);
				if (vertex_is_in_terminal_trees[u] == 0) {
					contracted_non_terminals.insert(contracted_non_terminals.end(), u);
				}
			}
		}

		contract_trees(contracted_edges, contracted_non_terminals, contracted_tree_IDs, terminal_trees,
			vertex_is_in_terminal_trees, g2, solution_graph); // contract_trees

	}


	boost_graph_transform_ec_nw_back(instance_graph, solution_graph);

	//cout << "terminal_trees.size():" << terminal_trees.size() << endl;
	//cout << "num_edges(solution_graph):" << num_edges(solution_graph) << endl;
	return solution_graph;

}
#pragma endregion Guha_16103




/*two relay node placement algorithms*/

#pragma region
graph GPrA_repaired(graph input_graph) {

	//This repaied version uses boost::tie(ai, a_end) = boost::adjacent_vertices(i, output_graph); to replace tie(eit, eend) = boost::out_edges(i, output_graph); // adjacent_vertices of i


	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;

	int N = num_vertices(input_graph); // number of vertices
	std::vector<double> nw1(N); // the nw value for finding R, it will be decreased after the check
	std::vector<double> nw2(N); // the nw value for pruning
	for (int i = 0; i < N; i++) {
		nw1[i] = get(boost::vertex_name_t(), input_graph, i);
		nw2[i] = get(boost::vertex_name_t(), input_graph, i);
	}
	std::vector<bool> pcheck1(N); // true means it has been checked 
	int num_check1 = 0; // the number of checked vertices to find R
	std::vector<bool> pcheck2(N); // true means it has been checked 
	int num_check2 = 0; // the number of checked vertices for pruning
	std::vector<int> pdegree1(N); // the processing degree to find R
	std::vector<int> pdegree2(N); // the processing degree for pruning
	std::vector<int> leaf1; // the leaves for finding R
	std::vector<int> leaf2; // the leaves for pruning

	for (int i = 0; i < N; i++) {
		pdegree1[i] = in_degree(i, input_graph); // decrease pdegree
		pdegree2[i] = pdegree1[i];
		if (pdegree1[i] == 0) {
			pcheck1[i] = true; // check disconnected vertices
			num_check1++;
			pcheck2[i] = true;
			num_check2++;
		}
		else if (pdegree1[i] == 1) {
			leaf1.insert(leaf1.end(), i);
			leaf2.insert(leaf2.end(), i);
		}
	}

	graph::out_edge_iterator eit, eend;
	AdjacencyIterator ai, a_end;
	int leaf_num1 = N - num_check1 - 1; // the number of leaves you need to process
	int leaf_num2 = N - num_check1 - 1; // the number of leaves you need to process


										//this version is similar to the version below
	int k = 0;
	while (k < leaf_num1) {
		int i = leaf1[k];
		k++;

		boost::tie(ai, a_end) = boost::adjacent_vertices(i, input_graph);
		for (; ai != a_end; ai++) {
			int j = *ai;
			if (pcheck1[j] == false) {
				double cost = get(boost::edge_weight_t(), input_graph, boost::edge(i, j, input_graph).first);
				if (cost < nw1[i]) {
					nw1[j] = nw1[j] + nw1[i] - cost; // decrease nw1[j]
				}
				pcheck1[i] = true; // i has been checked, there is no need to delete it in this phase
				pdegree1[j]--;// decrease pdegree[j]
				if (pdegree1[j] == 1) {
					leaf1.insert(leaf1.end(), j); // it's fine to insert in the end, but not in the biginning
				}
				// break; // how to break a for_each???
			}
		}

	}

	// R is the vertex with the biggest nw
	int R = 0;
	double max = nw1[0];
	for (int i = 1; i < N; i++) {
		if (nw1[i] > max) {
			max = nw1[i];
			R = i;
		}
	}


	//cout << "R=" << R << endl;

	// Strong pruning tree
	graph output_graph = input_graph; // the output graph

									  //this version is similar to the version below
	k = 0;
	while (k < leaf_num2 + 1) { // since R is ignored, it must be leaf_num2+1
		int i = leaf2[k];
		k++;
		if (i != R) {


			boost::tie(ai, a_end) = boost::adjacent_vertices(i, output_graph);
			for (; ai != a_end; ai++) {
				int j = *ai;
				if (pcheck2[j] == false) {
					double cost = get(boost::edge_weight_t(), output_graph, boost::edge(i, j, output_graph).first);
					if (cost < nw2[i]) {
						nw2[j] = nw2[j] + nw2[i] - cost; // decrease nw2[j]
					}
					else {
						boost::remove_edge(i, j, output_graph); // remove edge(i,j)

																//cout << "nw2[i]: " << nw2[i] << endl;
																//cout << "cost: " << cost << endl;
																//cout << "remove edge " << i << "," << j << endl;
					}
					pcheck2[i] = true; // i has been checked
					pdegree2[j]--;// decrease pdegree[j]
					if (pdegree2[j] == 1) {
						leaf2.insert(leaf2.end(), j);
					}
					break; // there may be an error without break;
				}
			}


		}
	}


	// deleted disconnected parts
	std::vector<int> component(N); // vertex i is in component[i]; No.component from 0
	int cpn_num = connected_components(output_graph, &component[0]); // the number of component; decrease component
	for (int i = 0; i < N; i++) {
		if (component[i] != component[R]) { // disconnected vertex
			clear_vertex(i, output_graph); // clear_vertex removes adjacent vertices, but not node weight
		}
	}


	return output_graph;

}
#pragma endregion GPrA_repaired 

#pragma region 
std::vector<int> SP_Yahui(graph g, int source, int destionation, double& SP_distance) {

	// Create things for Dijkstra
	std::vector<int> predecessors(boost::num_vertices(g)); // To store parents
	std::vector<double> distances(boost::num_vertices(g)); // To store distances
	typedef boost::property_map < graph, boost::vertex_index_t >::type IndexMap;
	IndexMap indexMap = boost::get(boost::vertex_index, g);
	typedef boost::iterator_property_map < int*, IndexMap, int, int& > PredecessorMap;
	PredecessorMap predecessorMap(&predecessors[0], indexMap);
	typedef boost::iterator_property_map < double*, IndexMap, double, double& > DistanceMap;
	DistanceMap distanceMap(&distances[0], indexMap);

	// Compute shortest paths from source to all vertices, and store the output in predecessors and distances
	boost::dijkstra_shortest_paths(g, source, boost::distance_map(distanceMap).predecessor_map(predecessorMap));

	// Extract a shortest path
	std::vector<int> path;
	path.insert(path.begin(), destionation);
	int v = destionation; // We want to start at the destination and work our way back to the source
	for (int u = predecessorMap[v]; // Start by setting 'u' to the destintaion node's predecessor
		u != v; // Keep tracking the path until we get to the source
		v = u, u = predecessorMap[v]) // Set the current vertex to the current predecessor, and the predecessor to one level up
	{
		path.insert(path.begin(), u);
	}

	SP_distance = distanceMap[destionation];
	return path;
}
#pragma endregion SP_Yahui 

#pragma region 
graph Simple_1981_algorithm_for_STPG(graph instance_graph, std::vector<int> terminal) {

	// this algorithm is in "A Fast Algorithm for Steiner Trees" 1981

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	typedef graph::edge_descriptor Edge;

	int N = num_vertices(instance_graph);

	std::vector<int> compulsory_terminals;
	for (int i = 0; i < N; i++) {
		if (terminal[i] == 1) {
			compulsory_terminals.insert(compulsory_terminals.end(), i); // terminal vector
		}
	}


	// Create things for Dijkstra
	std::vector<int> predecessors(N); // To store parents
	std::vector<double> distances(N); // To store distances
	typedef boost::property_map < graph, boost::vertex_index_t >::type IndexMap;
	IndexMap indexMap = boost::get(boost::vertex_index, instance_graph);
	typedef boost::iterator_property_map < int*, IndexMap, int, int& > PredecessorMap;
	PredecessorMap predecessorMap(&predecessors[0], indexMap);
	typedef boost::iterator_property_map < double*, IndexMap, double, double& > DistanceMap;
	DistanceMap distanceMap(&distances[0], indexMap);

	graph complete_graph(compulsory_terminals.size()); // distance complete graph
	for (int i = 0; i < compulsory_terminals.size(); i++) {
		// Compute shortest paths from source to all vertices, and store the output in predecessors and distances
		boost::dijkstra_shortest_paths(instance_graph, compulsory_terminals[i],
			boost::distance_map(distanceMap).predecessor_map(predecessorMap)); // all SPs to compulsory_terminals[i]
		for (int j = i + 1; j < compulsory_terminals.size(); j++) {
			boost::add_edge(i, j, distances[compulsory_terminals[j]], complete_graph);
		}
	}


	graph MST = boost_graph_find_MST(complete_graph); // MST

	graph raw_solution_graph(N);
	double SP_distance;
	for (int i = 0; i < compulsory_terminals.size(); i++) {
		boost::tie(ai, a_end) = boost::adjacent_vertices(i, MST);
		for (; ai != a_end; ai++) {
			if (i < *ai) {
				std::vector<int> Path = SP_Yahui(instance_graph, compulsory_terminals[i], compulsory_terminals[*ai], SP_distance);
				for (int k = 0; k < Path.size() - 1; k++) {
					int e1 = Path[k];
					int e2 = Path[k + 1];
					double ec = get(boost::edge_weight_t(), instance_graph, boost::edge(e1, e2, instance_graph).first);
					boost::add_edge(e1, e2, ec, raw_solution_graph); // replace edges in MST by SPs
				}
			}
		}
	}

	raw_solution_graph = boost_graph_find_MST(raw_solution_graph); // MST

	double total_ec_and_nw = boost_graph_sum_of_nw_and_ec(raw_solution_graph, N) + 1e5; // OSRP have zero ec, so total_ec_and_nw may be 0
	for (int i = 0; i < N; i++) {
		if (terminal[i] == 1) {
			boost::put(boost::vertex_name_t(), raw_solution_graph, i, 10 * total_ec_and_nw); // give large nw to terminal for GPrA below 
		}
	}
	raw_solution_graph = GPrA_repaired(raw_solution_graph); // remove non-terminal leaves

	return raw_solution_graph;


}
#pragma endregion Simple_1981_algorithm_for_STPG 

#pragma region 
graph RRPL_2017_outage_paper_algorithm_multiple_bs_sensor_can_connect_bs
(graph instance_graph, std::vector<int> terminal, std::vector<int> leaf_terminal) {

	graph::out_edge_iterator eit, eend;
	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	typedef graph::edge_descriptor Edge;

	int N = num_vertices(instance_graph);

	std::vector<int> base_stations;
	std::vector<int> new_terminal(N);
	for (int i = 0; i < N; i++) {
		if (terminal[i] == 1 && leaf_terminal[i] == 0) {
			new_terminal[i] = 1; // bs
			base_stations.insert(base_stations.end(), i);
		}
	}

	std::vector<int> existing_sensors = copy_vector_int(leaf_terminal); // sensors in the graph
	int existing_sensors_num = 0;
	for (int i = 0; i < N; i++) {
		if (leaf_terminal[i] == 1) {
			existing_sensors_num++;
		}
	}

	graph solu_graph = copy_graph(instance_graph);

	std::vector<pair<int, int>> rs_edges; // relay to sensor edges that need to be added

	std::vector<int> non_terminal_relay; // relays that have not been chosen to be terminal yet
	for (int i = 0; i < N; i++) {
		if (terminal[i] == 0) {
			non_terminal_relay.insert(non_terminal_relay.end(), i);
		}
	}


	// connected sensors to the closest bs
	for (int i = 0; i < N; i++) {
		if (leaf_terminal[i] == 1) { // i is sensor
			double min_distance = 1e9;
			int closest_bs = N;
			pair<Edge, bool> ed;
			for (int bs_ID = 0; bs_ID < base_stations.size(); bs_ID++) {
				ed = boost::edge(i, base_stations[bs_ID], instance_graph);
				if (ed.second) { // this edge exists
					double ec = get(boost::edge_weight_t(), instance_graph, boost::edge(i, base_stations[bs_ID], instance_graph).first);
					if (min_distance > ec) {
						min_distance = ec;
						closest_bs = base_stations[bs_ID];
					}

				}
			}
			if (min_distance < 1e9) {
				existing_sensors_num--;
				clear_vertex(i, solu_graph); // remove this sensor

											 //cout << "remove sensor:" << i << endl;


				existing_sensors[i] = 0; // this sensor has been removed
				pair<int, int> edge = { i , closest_bs };
				rs_edges.insert(rs_edges.end(), edge);
			}
		}
	}





	while (existing_sensors_num > 0) { // remove all sensors

		int best_relay_id;
		int max_adj_sensor_num = 0;
		double lowest_adj_ec = 1e30;

		for (int i = 0; i < non_terminal_relay.size(); i++) {
			int adj_sensor_num = 0;
			double adj_ec = 0;
			boost::tie(ai, a_end) = boost::adjacent_vertices(non_terminal_relay[i], instance_graph);
			for (; ai != a_end; ai++) {
				if (existing_sensors[*ai] == 1) {
					adj_sensor_num++;
					double ec = get(boost::edge_weight_t(), instance_graph, boost::edge(non_terminal_relay[i], *ai, instance_graph).first);
					adj_ec = adj_ec + ec;
				}
			}
			if (adj_sensor_num > max_adj_sensor_num) { // this relay connect more sensors
				max_adj_sensor_num = adj_sensor_num;
				lowest_adj_ec = adj_ec;
				best_relay_id = i;
			}
			else if (adj_sensor_num == max_adj_sensor_num && adj_ec < lowest_adj_ec) { // adj_ec is lower
				max_adj_sensor_num = adj_sensor_num;
				lowest_adj_ec = adj_ec;
				best_relay_id = i;
			}
		}

		boost::tie(ai, a_end) = boost::adjacent_vertices(non_terminal_relay[best_relay_id], instance_graph);
		for (; ai != a_end; ai++) {
			if (existing_sensors[*ai] == 1) {
				existing_sensors_num--;
				clear_vertex(*ai, solu_graph); // remove this sensor

											   //cout << "remove sensor:" << *ai << endl;


				existing_sensors[*ai] = 0; // this sensor has been removed
				pair<int, int> edge = { *ai , non_terminal_relay[best_relay_id] };
				rs_edges.insert(rs_edges.end(), edge);
			}
		}

		new_terminal[non_terminal_relay[best_relay_id]] = 1; // new relay terminal

															 //cout << "non_terminal_relay.size():" << non_terminal_relay.size() << endl;
															 //cout << "non_terminal_relay[best_relay_id]:" << non_terminal_relay[best_relay_id] << endl;
															 //cout << "existing_sensors_num:" << existing_sensors_num << endl;

		non_terminal_relay.erase(non_terminal_relay.begin() + best_relay_id);

	}

	//cout << "in_degree(0, solu_graph): " << in_degree(0, solu_graph) << endl;

	solu_graph = Simple_1981_algorithm_for_STPG(solu_graph, new_terminal); // it's much faster than OSRP_2016 since relay_terminal_num is smaller than sensor_terminal_num

																		   //cout << "in_degree(0, solu_graph): " << in_degree(0, solu_graph) << endl;


	for (int i = 0; i < rs_edges.size(); i++) {
		int e1 = rs_edges[i].first;
		int e2 = rs_edges[i].second;
		pair<Edge, bool> ed = boost::edge(e1, e2, solu_graph);
		if (!ed.second) { // this edge does not exist
			boost::add_edge(e1, e2, 1, solu_graph);
		}
	}


	// increase sensor-relay ec
	double total_ec_and_nw = boost_graph_sum_of_nw_and_ec(instance_graph, num_vertices(instance_graph));
	graph transformed_instance_graph = copy_graph(instance_graph);
	transform_NWPFSTP_instance(transformed_instance_graph, leaf_terminal, total_ec_and_nw);
	boost_graph_MST_postprocessing(transformed_instance_graph, solu_graph);


	boost_graph_transform_ec_nw_back(instance_graph, solu_graph); // tranform ec and nw back


	return solu_graph;

}
#pragma endregion RRPL_2017_outage_paper_algorithm_multiple_bs_sensor_can_connect_bs

#pragma region 
graph OSRP_2016_IEEEletter_paper_algorithm_sensor_can_connect_bs(graph instance_graph, std::vector<int> terminal, std::vector<int> leaf_terminal) {

	graph::out_edge_iterator eit, eend;
	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	typedef graph::edge_descriptor Edge;

	int N = num_vertices(instance_graph);

	graph solu_graph = copy_graph(instance_graph);

	for (int i = 0; i < N; i++) {
		if (terminal[i] == 1 && leaf_terminal[i] == 0) { // i is bs
			boost::tie(ai, a_end) = boost::adjacent_vertices(i, solu_graph);
			for (; ai != a_end; ai++) {
				if (terminal[*ai] == 1) { // *ai is sensor or bs
					pair<Edge, bool> ed = boost::edge(i, *ai, solu_graph);
					boost::put(boost::edge_weight_t(), solu_graph, ed.first, 0); // change ec for edges between bs and r
				}
				else if (terminal[*ai] == 0) { // *ai is relay
					pair<Edge, bool> ed = boost::edge(i, *ai, solu_graph);
					boost::put(boost::edge_weight_t(), solu_graph, ed.first, 1); // change ec for edges between bs and r
				}
			}
		}
		else if (terminal[i] == 0) { // i is r
			boost::tie(ai, a_end) = boost::adjacent_vertices(i, solu_graph);
			for (; ai != a_end; ai++) {
				if (terminal[*ai] == 0) { // *ai is r
					pair<Edge, bool> ed = boost::edge(i, *ai, solu_graph);
					boost::put(boost::edge_weight_t(), solu_graph, ed.first, 2); // change ec for edges between r and r
				}
				else if (leaf_terminal[*ai] == 1) { // *ai is s
					pair<Edge, bool> ed = boost::edge(i, *ai, solu_graph);
					boost::put(boost::edge_weight_t(), solu_graph, ed.first, N); // change ec for edges between s and r
				}
			}
		}
	}


	solu_graph = Simple_1981_algorithm_for_STPG(solu_graph, terminal);


	// increase sensor-relay ec
	double total_ec_and_nw = boost_graph_sum_of_nw_and_ec(instance_graph, num_vertices(instance_graph));
	graph transformed_instance_graph = copy_graph(instance_graph);
	transform_NWPFSTP_instance(transformed_instance_graph, leaf_terminal, total_ec_and_nw);
	boost_graph_MST_postprocessing(transformed_instance_graph, solu_graph);


	boost_graph_transform_ec_nw_back(instance_graph, solu_graph); // tranform ec and nw back


	return solu_graph;


}
#pragma endregion OSRP_2016_IEEEletter_paper_algorithm_sensor_can_connect_bs



/*WSNs*/

#pragma region 
graph generate_CCG_grid_multipleBS(graph& distance_graph, std::vector<int>& terminal, std::vector<int>& leaf_terminal,
	int B_target, int R_target, int S_target, int min_relay_nw, int max_relay_nw,
	double sensitivity_rth, double P_S, double P_R, double reference_distance, double b_a,
	int Euclidean_x_max, int Euclidean_y_max, double& valid_ratio) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end, bi, b_end, ci, c_end;
	typedef graph::edge_descriptor Edge;

	// parameters
	int Euclidean_x_min = 0;
	int Euclidean_y_min = 0;
	int N = R_target + S_target + B_target; terminal.resize(N); leaf_terminal.resize(N);
	double range_S = reference_distance * sqrt(P_S / sensitivity_rth); // 2017 outage model for transmission ranges
	double range_R = reference_distance * sqrt(P_R / sensitivity_rth); // 2017 outage model for transmission ranges

	// generate graph edges without costs
	bool connected = false;
	graph output_graph;
	std::vector<int> node_type(N); // 0:sensor, 100:basestation, 1:relay
	std::vector<std::vector<double>> visualization_coordinate;
	while (connected == false) {

		graph WSN_two_tiered;
		bool solvable = false;
		while (solvable == false) {

			graph temporary_graph(N);

			// distribute locations; ec is not solvable for vertices with too large degrees
			std::vector<std::vector<double>> Euclidean_location_relay;
			std::vector<std::vector<double>> Euclidean_location_basestation;
			std::vector<std::vector<double>> Euclidean_location_sensor;
			std::vector<std::vector<double>> available_locations;
			for (int i = 0; i <= sqrt(N) + 1; i++) {
				for (int j = 0; j <= sqrt(N) + 1; j++) {
					std::vector<double> node;
					node.insert(node.end(), i * Euclidean_x_max / (sqrt(N) + 1) + (rand() % Euclidean_x_max / (sqrt(N) + 1)) / 2);
					node.insert(node.end(), j * Euclidean_y_max / (sqrt(N) + 1) + (rand() % Euclidean_y_max / (sqrt(N) + 1)) / 2);
					available_locations.insert(available_locations.end(), node);
				}
			}
			// base location 
			while (Euclidean_location_basestation.size() < B_target) {
				int rand_location = rand() % available_locations.size();
				Euclidean_location_basestation.insert(Euclidean_location_basestation.end(), available_locations[rand_location]);
				available_locations.erase(available_locations.begin() + rand_location);
			}
			// R location
			while (Euclidean_location_relay.size() < R_target) {
				int rand_location = rand() % available_locations.size();
				Euclidean_location_relay.insert(Euclidean_location_relay.end(), available_locations[rand_location]);
				available_locations.erase(available_locations.begin() + rand_location);
			}
			// sensor location
			while (Euclidean_location_sensor.size() < S_target) {
				int rand_location = rand() % available_locations.size();
				Euclidean_location_sensor.insert(Euclidean_location_sensor.end(), available_locations[rand_location]);
				available_locations.erase(available_locations.begin() + rand_location);
			}

			// generate graph nodes
			visualization_coordinate.clear();
			int node_index = 0;
			for (int i = 0; i < Euclidean_location_basestation.size(); i++) {  // make the basestation
				std::vector<double> coordinate;
				coordinate.insert(coordinate.end(), Euclidean_location_basestation[i][0]);
				coordinate.insert(coordinate.end(), Euclidean_location_basestation[i][1]);
				visualization_coordinate.insert(visualization_coordinate.end(), coordinate);
				terminal[node_index] = 1; // compulsory terminal
				leaf_terminal[node_index] = 0; // non-leaf compulsory terminal
				node_type[node_index] = 100; // bs
				boost::put(boost::vertex_name_t(), temporary_graph, node_index, 0);
				node_index++;
			}
			for (int i = 0; i < Euclidean_location_sensor.size(); i++) {  // sensor
				std::vector<double> coordinate;
				coordinate.insert(coordinate.end(), Euclidean_location_sensor[i][0]);
				coordinate.insert(coordinate.end(), Euclidean_location_sensor[i][1]);
				visualization_coordinate.insert(visualization_coordinate.end(), coordinate);
				terminal[node_index] = 1; // compulsory terminal
				leaf_terminal[node_index] = 1; // leaf compulsory terminal
				node_type[node_index] = 0; // s
				boost::put(boost::vertex_name_t(), temporary_graph, node_index, 0);
				node_index++;
			}
			for (int i = 0; i < Euclidean_location_relay.size(); i++) {  // relay
				std::vector<double> coordinate;
				coordinate.insert(coordinate.end(), Euclidean_location_relay[i][0]);
				coordinate.insert(coordinate.end(), Euclidean_location_relay[i][1]);
				visualization_coordinate.insert(visualization_coordinate.end(), coordinate);
				terminal[node_index] = 0; // non-compulsory terminal
				leaf_terminal[node_index] = 0; // non-leaf compulsory terminal
				node_type[node_index] = 1; // r
				double nw = (double)(min_relay_nw + (rand() % (int)(max_relay_nw - min_relay_nw + 1)));
				double normalized_nw = (double)(nw - min_relay_nw) / (max_relay_nw - min_relay_nw);
				//cout << nw << endl;
				//getchar();
				boost::put(boost::vertex_name_t(), temporary_graph, node_index, b_a * normalized_nw);
				node_index++;
			}

			// add edge phase 1
			for (int i = 0; i < N; i++) {
				if (node_type[i] > 0) { // i is base station or relay 
					for (int j = i + 1; j < N; j++) {
						if (node_type[j] > 0) { // base station or relay
							double distance = sqrt(pow(visualization_coordinate[i][0] - visualization_coordinate[j][0], 2) +
								pow(visualization_coordinate[i][1] - visualization_coordinate[j][1], 2));
							if (distance <= range_R) { // range of relay
								boost::add_edge(j, i, 1, temporary_graph);
							}
							else if (node_type[i] + node_type[j] == 200) { // two base stations connect each other
								boost::add_edge(j, i, 1, temporary_graph);
							}
						}
					}
				}
			}
			std::vector<int> component(N); // vertex i is in component[i]; No.component from 0
			int cpn_num = connected_components(temporary_graph, &component[0]); // the number of component; decrease component
			if (cpn_num == S_target + 1) { // CCG is solvable, so, go on!
				solvable = true;
				WSN_two_tiered = copy_graph(temporary_graph);
			}
			else {
				cout << "Unsolvable!" << endl;
			}
		}

		output_graph = copy_graph(WSN_two_tiered);

		// add edge phase 2
		for (int i = 0; i < N; i++) {
			if (node_type[i] == 0) { // i is sensor
				for (int j = 0; j < N; j++) {
					if (node_type[j] > 0) { // j is relay or base station
						double distance = sqrt(pow(visualization_coordinate[i][0] - visualization_coordinate[j][0], 2) +
							pow(visualization_coordinate[i][1] - visualization_coordinate[j][1], 2));
						if (distance <= range_S) { // sensor i connects its nearby relay; we assume that range_S<=range_R
							boost::add_edge(i, j, 1, output_graph);
						}
					}
				}
			}
		}

		distance_graph = copy_graph(output_graph);

		// generate graph edge costs
		for (int u = 0; u < N; u++) {
			boost::tie(ai, a_end) = boost::adjacent_vertices(u, output_graph);
			for (; ai != a_end; ai++) {
				int v = *ai;
				if (u < v) {

					pair<Edge, bool> ed = boost::edge(u, v, output_graph);

					double duv = sqrt(pow(visualization_coordinate[u][0] - visualization_coordinate[v][0], 2) +
						pow(visualization_coordinate[u][1] - visualization_coordinate[v][1], 2));

					pair<Edge, bool> ed2 = boost::edge(u, v, distance_graph);
					boost::put(boost::edge_weight_t(), distance_graph, ed2.first, duv);

					if (node_type[u] == 100 && node_type[v] == 100) {
						boost::put(boost::edge_weight_t(), output_graph, ed.first, 0); // base station have small-cost edge between each other
					}
					else {

						// 2017 outage model for transmission costs
						double probability_uv = 1;
						double probability_vu = 1;
						double signal_noise_ratio_ruv;
						if (node_type[u] == 0) {
							signal_noise_ratio_ruv = P_S / pow(duv / reference_distance, 2);
						}
						else if (node_type[u] == 1) {
							signal_noise_ratio_ruv = P_R / pow(duv / reference_distance, 2);
						}
						else if (node_type[u] == 100) {
							signal_noise_ratio_ruv = 100 * P_R / pow(duv / reference_distance, 2);
						}

						boost::tie(bi, b_end) = boost::adjacent_vertices(v, output_graph); // only count adjacent transmitting nodes since others are not in the range
						for (; bi != b_end; bi++) {
							int t = *bi;
							if (t != u && t != v) {
								double dtv = sqrt(pow(visualization_coordinate[t][0] - visualization_coordinate[v][0], 2) +
									pow(visualization_coordinate[t][1] - visualization_coordinate[v][1], 2));

								double signal_noise_ratio_rtv;
								if (node_type[t] == 0) {
									signal_noise_ratio_rtv = P_S / pow(dtv / reference_distance, 2);
								}
								else if (node_type[t] == 1) {
									signal_noise_ratio_rtv = P_R / pow(dtv / reference_distance, 2);
								}
								else if (node_type[t] == 100) {
									signal_noise_ratio_rtv = 1e10 * P_R / pow(dtv / reference_distance, 2);
								}

								boost::tie(ci, c_end) = boost::adjacent_vertices(v, output_graph);
								double ctv = 1;
								for (; ci != c_end; ci++) {
									int z = *ci;
									if (z != u && z != v && z != t) {
										double dzv = sqrt(pow(visualization_coordinate[z][0] - visualization_coordinate[v][0], 2) +
											pow(visualization_coordinate[z][1] - visualization_coordinate[v][1], 2));

										double signal_noise_ratio_rzv;
										if (node_type[z] == 0) {
											signal_noise_ratio_rzv = P_S / pow(dzv / reference_distance, 2);
										}
										else if (node_type[z] == 1) {
											signal_noise_ratio_rzv = P_R / pow(dzv / reference_distance, 2);
										}
										else if (node_type[z] == 100) {
											signal_noise_ratio_rzv = 1e10 * P_R / pow(dzv / reference_distance, 2);
										}

										ctv = ctv * signal_noise_ratio_rtv / (signal_noise_ratio_rtv - signal_noise_ratio_rzv);
									}
								}
								//cout << "ctv:" << ctv << endl;
								probability_uv = probability_uv - ctv * signal_noise_ratio_ruv /
									(signal_noise_ratio_ruv + signal_noise_ratio_rtv * sensitivity_rth)*
									exp(-sensitivity_rth / signal_noise_ratio_ruv);
								/*the 2017 outage model may not always induce feasible outage
								probabilities; the negative p and large p are 
								removed below for producing instances similar to the 2017 ones*/
								if (probability_uv > 0.95) { 
									probability_uv = 0.7 + (double)(rand() % 2000) * 1e-4;
								}
								else if (probability_uv < 0) { 
									probability_uv = 0.0 + (double)(rand() % 2000) * 1e-4;
								}
							}
						}

						boost::tie(bi, b_end) = boost::adjacent_vertices(u, output_graph); // only count adjacent transmitting nodes since others are not in the range
						for (; bi != b_end; bi++) {
							int t = *bi;
							if (t != u && t != v) {
								double dtu = sqrt(pow(visualization_coordinate[t][0] - visualization_coordinate[u][0], 2) +
									pow(visualization_coordinate[t][1] - visualization_coordinate[u][1], 2));

								double signal_noise_ratio_rtu;
								if (node_type[t] == 0) {
									signal_noise_ratio_rtu = P_S / pow(dtu / reference_distance, 2);
								}
								else if (node_type[t] == 1) {
									signal_noise_ratio_rtu = P_R / pow(dtu / reference_distance, 2);
								}
								else if (node_type[t] == 100) {
									signal_noise_ratio_rtu = 1e10 * P_R / pow(dtu / reference_distance, 2);
								}

								boost::tie(ci, c_end) = boost::adjacent_vertices(u, output_graph);
								double ctu = 1;
								for (; ci != c_end; ci++) {
									int z = *ci;
									if (node_type[z] != 100 && z != u && z != v && z != t) {
										double dzu = sqrt(pow(visualization_coordinate[z][0] - visualization_coordinate[u][0], 2) +
											pow(visualization_coordinate[z][1] - visualization_coordinate[u][1], 2));

										double signal_noise_ratio_rzu;
										if (node_type[z] == 0) {
											signal_noise_ratio_rzu = P_S / pow(dzu / reference_distance, 2);
										}
										else if (node_type[z] == 1) {
											signal_noise_ratio_rzu = P_R / pow(dzu / reference_distance, 2);
										}
										else if (node_type[z] == 100) {
											signal_noise_ratio_rzu = 1e10 * P_R / pow(dzu / reference_distance, 2);
										}

										ctu = ctu * signal_noise_ratio_rtu / (signal_noise_ratio_rtu - signal_noise_ratio_rzu);
									}
								}
								//cout << "ctu:" << ctu << endl;
								probability_vu = probability_vu - ctu * signal_noise_ratio_ruv /
									(signal_noise_ratio_ruv + signal_noise_ratio_rtu * sensitivity_rth)*
									exp(-sensitivity_rth / signal_noise_ratio_ruv);
								if (probability_vu > 0.95) {
									probability_vu = 0.7 + (double)(rand() % 2000) * 1e-4;
								}
								else if (probability_vu < 0) {
									probability_vu = 0.0 + (double)(rand() % 2000) * 1e-4;
								}
							}
						}
						boost::put(boost::edge_weight_t(), output_graph, ed.first, (probability_uv + probability_vu) / 2);

					}

				}
			}
		}

		/*connectivity check*/
		std::vector<int> component(N);
		int cpn_num = connected_components(output_graph, &component[0]); // the number of component; decrease component
		int cpn_num2 = connected_components(WSN_two_tiered, &component[0]); // the number of component; decrease component

		if (cpn_num == 1 && cpn_num2 == S_target + 1) {
			connected = true;
		}
		else {
			cout << "Disconnected!" << endl;
		}

	}

	return output_graph;

}
#pragma endregion generate_CCG_grid_multipleBS 

#pragma region 
graph put_all_transmission_routes_in_solu_graph(graph& instance_graph, graph solu_graph) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	typedef graph::edge_descriptor Edge;

	int N = num_vertices(solu_graph);

	for (int i = 0; i < N; i++) {
		if (in_degree(i, solu_graph) > 0) { // i is in solu_graph
			boost::tie(ai, a_end) = boost::adjacent_vertices(i, instance_graph); // edge (i,*ai) is in instance_graph
			for (; ai != a_end; ai++) {
				if (in_degree(*ai, solu_graph) > 0 && i < *ai) { // *ai is in solu_graph
					pair<Edge, bool> ed = boost::edge(i, *ai, solu_graph);
					if (!ed.second) { // edge (i,*ai) does not exist in solu_graph
						boost::add_edge(i, *ai,
							get(boost::edge_weight_t(), instance_graph, boost::edge(i, *ai, instance_graph).first),
							solu_graph); // add edge (i,*ai) into solu_graph
					}
				}
			}
		}
	}

	return solu_graph;


}
#pragma endregion put_all_transmission_routes_in_solu_graph 

#pragma region 
double relay_cost(int N, graph& solution_graph, double b_a, std::vector<int>& terminal, int min_relay_nw, int max_relay_nw) {

	double deployed_relay_cost = 0;

	for (int i = 0; i < N; i++) {
		if (in_degree(i, solution_graph) > 0 && terminal[i] == 0) {
			double nw = get(boost::vertex_name_t(), solution_graph, i) / b_a; // it's normalized nw
			double cost = (double)nw * (max_relay_nw - min_relay_nw) + min_relay_nw;
			deployed_relay_cost = deployed_relay_cost + cost; // it's positive nw
		}
	}

	return deployed_relay_cost;

}
#pragma endregion relay_cost

#pragma region 
void WSN_performance_min_sum_of_p(graph instance_graph, graph solu_graph,
	std::vector<int> terminal, std::vector<int> leaf_terminal, double delay_p,
	std::vector<int> retransmission_Mr, double& net_lifetime, std::vector<double>& delay, std::vector<double>& goodput,
	double& average_route_length, double& average_route_p) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	typedef graph::edge_descriptor Edge;

	double sensor_transmission_times = 1e7;
	int R1 = 1; // the rate of the first automatic repeat request transmission in bits per channel use

	int N = num_vertices(solu_graph);

	graph solu_graph_with_all_transmission_routes = put_all_transmission_routes_in_solu_graph(instance_graph, solu_graph);

	// increase sensor-relay ec
	double total_ec_and_nw = boost_graph_sum_of_nw_and_ec(instance_graph, num_vertices(instance_graph));
	graph transformed_instance_graph = copy_graph(solu_graph_with_all_transmission_routes);
	transform_NWPFSTP_instance(transformed_instance_graph, leaf_terminal, total_ec_and_nw);

	std::vector<int> base_stations;
	for (int i = 0; i < N; i++) {
		if (terminal[i] == 1 && leaf_terminal[i] == 0) {
			base_stations.insert(base_stations.end(), i);
		}
	}


	// Create things for Dijkstra
	std::vector<std::vector<int>> predecessors(base_stations.size()); // To store parents
	std::vector<std::vector<double>> distances(base_stations.size()); // To store distances
	typedef boost::property_map < graph, boost::vertex_index_t >::type IndexMap;
	typedef boost::iterator_property_map < int*, IndexMap, int, int& > PredecessorMap;
	for (int bs_ID = 0; bs_ID < base_stations.size(); bs_ID++) {
		predecessors[bs_ID].resize(N);
		distances[bs_ID].resize(N);
		IndexMap indexMap = boost::get(boost::vertex_index, transformed_instance_graph); // transformed_instance_graph ensure two-tiered
		PredecessorMap predecessorMap(&predecessors[bs_ID][0], indexMap);
		typedef boost::iterator_property_map < double*, IndexMap, double, double& > DistanceMap;
		DistanceMap distanceMap(&distances[bs_ID][0], indexMap);
		// Compute shortest paths from source to all vertices, and store the output in predecessors and distances
		boost::dijkstra_shortest_paths(transformed_instance_graph, base_stations[bs_ID],
			boost::distance_map(distanceMap).predecessor_map(predecessorMap)); // all SPs to base_stations[bs_ID]
	}



	int Mr_num = retransmission_Mr.size();
	double average_efficiency = 0;
	std::vector<double> average_goodput(Mr_num);
	std::vector<double> average_delay(Mr_num);
	int sensor_num = 0;
	int sum_route_length = 0;
	double sum_route_p = 0;

	for (int j = 0; j < N; j++) {
		if (leaf_terminal[j] == 1) { // j is a sensor
			sensor_num++;


			double SP_dis_to_bs = 1e19;
			int SP_bs = 0;
			for (int bs_ID = 0; bs_ID < base_stations.size(); bs_ID++) {
				if (in_degree(base_stations[bs_ID], solu_graph_with_all_transmission_routes) > 0
					&& distances[bs_ID][j] < SP_dis_to_bs) {
					SP_dis_to_bs = distances[bs_ID][j];
					SP_bs = bs_ID;
				}
			}


			int adj_relay = predecessors[SP_bs][j];
			double ec = get(boost::edge_weight_t(), instance_graph, boost::edge(j, adj_relay, instance_graph).first);
			double efficiency = R1 * (1 - ec);
			average_efficiency = average_efficiency + efficiency;

			

			for (int x = 0; x < Mr_num; x++) {
				double goodput_this_sensor = 1;
				double delay_this_sensor = 0;
				int destionation = j;
				int v = destionation; // We want to start at the destination and work our way back to the source
				for (int u = predecessors[SP_bs][v]; // Start by setting 'u' to the destintaion node's predecessor
					u != v; // Keep tracking the path until we get to the source
					v = u, u = predecessors[SP_bs][v]) // Set the current vertex to the current predecessor, and the predecessor to one level up
				{
					sum_route_length++;
					double ec = get(boost::edge_weight_t(), instance_graph, boost::edge(u, v, instance_graph).first);
					sum_route_p = sum_route_p + ec;
					double goodput_this_edge = 1 - pow(ec, retransmission_Mr[x]);
					goodput_this_sensor = goodput_this_sensor * goodput_this_edge;
					// calculate delay
					double ETr = (1 - pow(ec, retransmission_Mr[x])) / (1 - ec);
					double lambada = delay_p / ETr;
					double ETr2 = (1 - (2 * retransmission_Mr[x] - 1)*pow(ec, retransmission_Mr[x])) / (1 - ec) +
						2 * ec*(1 - pow(ec, retransmission_Mr[x] - 1)) / pow(1 - ec, 2);
					double T_soj = lambada * ETr2 / 2 / (1 - delay_p) + 1 / 2 + ETr;
					delay_this_sensor = delay_this_sensor + T_soj;
					if (terminal[u] == 1 && leaf_terminal[u] == 0) { // u is bs
						break;
					}
				}
				average_goodput[x] = average_goodput[x] + goodput_this_sensor;
				average_delay[x] = average_delay[x] + delay_this_sensor;
				//cout << "route_length: " << route_length << endl;
			}

		}
	}


	average_efficiency = average_efficiency / sensor_num;
	net_lifetime = sensor_transmission_times * average_efficiency;

	average_route_length = (double)sum_route_length / (sensor_num*Mr_num);
	average_route_p = (double)sum_route_p / sum_route_length;
	//cout << "average_route_length: " << average_route_length << endl;
	//cout << "average_route_p: " << average_route_p << endl;
	//getchar();


	for (int x = 0; x < Mr_num; x++) {
		average_goodput[x] = average_goodput[x] / sensor_num;
		average_delay[x] = average_delay[x] / sensor_num;
	}
	goodput = average_goodput;
	delay = average_delay;


}
#pragma endregion WSN_performance_min_sum_of_p

#pragma region 
void WSN_performance_routing_tree(graph instance_graph, graph solu_graph,
	std::vector<int> terminal, std::vector<int> leaf_terminal, double delay_p,
	std::vector<int> retransmission_Mr, double& net_lifetime, std::vector<double>& delay, std::vector<double>& goodput) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	typedef graph::edge_descriptor Edge;

	double sensor_transmission_times = 1e7;
	int R1 = 1; // the rate of the first automatic repeat request transmission in bits per channel use

	int N = num_vertices(solu_graph);

	// increase sensor-relay ec
	double total_ec_and_nw = boost_graph_sum_of_nw_and_ec(instance_graph, num_vertices(instance_graph));
	graph transformed_instance_graph = copy_graph(solu_graph);
	transform_NWPFSTP_instance(transformed_instance_graph, leaf_terminal, total_ec_and_nw);

	std::vector<int> base_stations;
	for (int i = 0; i < N; i++) {
		if (terminal[i] == 1 && leaf_terminal[i] == 0) {
			base_stations.insert(base_stations.end(), i);
		}
	}


	// Create things for Dijkstra
	std::vector<std::vector<int>> predecessors(base_stations.size()); // To store parents
	std::vector<std::vector<double>> distances(base_stations.size()); // To store distances
	typedef boost::property_map < graph, boost::vertex_index_t >::type IndexMap;
	typedef boost::iterator_property_map < int*, IndexMap, int, int& > PredecessorMap;
	for (int bs_ID = 0; bs_ID < base_stations.size(); bs_ID++) {
		predecessors[bs_ID].resize(N);
		distances[bs_ID].resize(N);
		IndexMap indexMap = boost::get(boost::vertex_index, transformed_instance_graph); // transformed_instance_graph ensure two-tiered
		PredecessorMap predecessorMap(&predecessors[bs_ID][0], indexMap);
		typedef boost::iterator_property_map < double*, IndexMap, double, double& > DistanceMap;
		DistanceMap distanceMap(&distances[bs_ID][0], indexMap);
		// Compute shortest paths from source to all vertices, and store the output in predecessors and distances
		boost::dijkstra_shortest_paths(transformed_instance_graph, base_stations[bs_ID],
			boost::distance_map(distanceMap).predecessor_map(predecessorMap)); // all SPs to base_stations[bs_ID]
	}



	int Mr_num = retransmission_Mr.size();
	double average_efficiency = 0;
	std::vector<double> average_goodput(Mr_num);
	std::vector<double> average_delay(Mr_num);
	int sensor_num = 0;

	for (int j = 0; j < N; j++) {
		if (leaf_terminal[j] == 1) { // j is a sensor
			sensor_num++;


			double SP_dis_to_bs = 1e19;
			int SP_bs = 0;
			for (int bs_ID = 0; bs_ID < base_stations.size(); bs_ID++) {
				if (in_degree(base_stations[bs_ID], transformed_instance_graph) > 0
					&& distances[bs_ID][j] < SP_dis_to_bs) {
					SP_dis_to_bs = distances[bs_ID][j];
					SP_bs = bs_ID;
				}
			}


			int adj_relay = predecessors[SP_bs][j];
			double ec = get(boost::edge_weight_t(), instance_graph, boost::edge(j, adj_relay, instance_graph).first);
			double efficiency = R1 * (1 - ec);
			average_efficiency = average_efficiency + efficiency;

			for (int x = 0; x < Mr_num; x++) {
				double goodput_this_sensor = 1;
				double delay_this_sensor = 0;
				int destionation = j;
				int v = destionation; // We want to start at the destination and work our way back to the source
				for (int u = predecessors[SP_bs][v]; // Start by setting 'u' to the destintaion node's predecessor
					u != v; // Keep tracking the path until we get to the source
					v = u, u = predecessors[SP_bs][v]) // Set the current vertex to the current predecessor, and the predecessor to one level up
				{
					double ec = get(boost::edge_weight_t(), instance_graph, boost::edge(u, v, instance_graph).first);
					double goodput_this_edge = 1 - pow(ec, retransmission_Mr[x]);
					goodput_this_sensor = goodput_this_sensor * goodput_this_edge;
					// calculate delay
					double ETr = (1 - pow(ec, retransmission_Mr[x])) / (1 - ec);
					double lambada = delay_p / ETr;
					double ETr2 = (1 - (2 * retransmission_Mr[x] - 1)*pow(ec, retransmission_Mr[x])) / (1 - ec) +
						2 * ec*(1 - pow(ec, retransmission_Mr[x] - 1)) / pow(1 - ec, 2);
					double T_soj = lambada * ETr2 / 2 / (1 - delay_p) + 1 / 2 + ETr;
					delay_this_sensor = delay_this_sensor + T_soj;
					if (terminal[u] == 1 && leaf_terminal[u] == 0) { // u is bs
						break;
					}
				}
				average_goodput[x] = average_goodput[x] + goodput_this_sensor;
				average_delay[x] = average_delay[x] + delay_this_sensor;
			}

		}
	}


	average_efficiency = average_efficiency / sensor_num;
	net_lifetime = sensor_transmission_times * average_efficiency;

	for (int x = 0; x < Mr_num; x++) {
		average_goodput[x] = average_goodput[x] / sensor_num;
		average_delay[x] = average_delay[x] / sensor_num;
	}
	goodput = average_goodput;
	delay = average_delay;


}
#pragma endregion WSN_performance_routing_tree

#pragma region 
void WSN_performance_SP(graph instance_graph, graph distance_graph, graph solu_graph,
	std::vector<int> terminal, std::vector<int> leaf_terminal, double delay_p,
	std::vector<int> retransmission_Mr, double& net_lifetime, std::vector<double>& delay, std::vector<double>& goodput) {

	typedef boost::graph_traits<graph>::adjacency_iterator AdjacencyIterator;
	AdjacencyIterator ai, a_end;
	typedef graph::edge_descriptor Edge;

	double sensor_transmission_times = 1e7;
	int R1 = 1; // the rate of the first automatic repeat request transmission in bits per channel use

	int N = num_vertices(solu_graph);

	graph solu_graph_with_all_transmission_routes = put_all_transmission_routes_in_solu_graph(instance_graph, solu_graph);

	// increase sensor-relay ec
	double total_ec_and_nw = boost_graph_sum_of_nw_and_ec(instance_graph, num_vertices(instance_graph));
	graph transformed_instance_graph = copy_graph(solu_graph_with_all_transmission_routes);
	boost_graph_transform_ec_nw_back(distance_graph, transformed_instance_graph); // transformed_instance_graph contains distances
	transform_NWPFSTP_instance(transformed_instance_graph, leaf_terminal, total_ec_and_nw);

	std::vector<int> base_stations;
	for (int i = 0; i < N; i++) {
		if (terminal[i] == 1 && leaf_terminal[i] == 0) {
			base_stations.insert(base_stations.end(), i);
		}
	}


	// Create things for Dijkstra
	std::vector<std::vector<int>> predecessors(base_stations.size()); // To store parents
	std::vector<std::vector<double>> distances(base_stations.size()); // To store distances
	typedef boost::property_map < graph, boost::vertex_index_t >::type IndexMap;
	typedef boost::iterator_property_map < int*, IndexMap, int, int& > PredecessorMap;
	for (int bs_ID = 0; bs_ID < base_stations.size(); bs_ID++) {
		predecessors[bs_ID].resize(N);
		distances[bs_ID].resize(N);
		IndexMap indexMap = boost::get(boost::vertex_index, transformed_instance_graph); // transformed_instance_graph ensure two-tiered
		PredecessorMap predecessorMap(&predecessors[bs_ID][0], indexMap);
		typedef boost::iterator_property_map < double*, IndexMap, double, double& > DistanceMap;
		DistanceMap distanceMap(&distances[bs_ID][0], indexMap);
		// Compute shortest paths from source to all vertices, and store the output in predecessors and distances
		boost::dijkstra_shortest_paths(transformed_instance_graph, base_stations[bs_ID],
			boost::distance_map(distanceMap).predecessor_map(predecessorMap)); // all SPs to base_stations[bs_ID]
	}



	int Mr_num = retransmission_Mr.size();
	double average_efficiency = 0;
	std::vector<double> average_goodput(Mr_num);
	std::vector<double> average_delay(Mr_num);
	int sensor_num = 0;

	for (int j = 0; j < N; j++) {
		if (leaf_terminal[j] == 1) { // j is a sensor
			sensor_num++;


			double SP_dis_to_bs = 1e19;
			int SP_bs = 0;
			for (int bs_ID = 0; bs_ID < base_stations.size(); bs_ID++) {
				if (in_degree(base_stations[bs_ID], solu_graph_with_all_transmission_routes) > 0
					&& distances[bs_ID][j] < SP_dis_to_bs) {
					SP_dis_to_bs = distances[bs_ID][j];
					SP_bs = bs_ID;
				}
			}


			int adj_relay = predecessors[SP_bs][j];
			double ec = get(boost::edge_weight_t(), instance_graph, boost::edge(j, adj_relay, instance_graph).first);
			double efficiency = R1 * (1 - ec);
			average_efficiency = average_efficiency + efficiency;

			for (int x = 0; x < Mr_num; x++) {
				double goodput_this_sensor = 1;
				double delay_this_sensor = 0;
				int destionation = j;
				int v = destionation; // We want to start at the destination and work our way back to the source
				for (int u = predecessors[SP_bs][v]; // Start by setting 'u' to the destintaion node's predecessor
					u != v; // Keep tracking the path until we get to the source
					v = u, u = predecessors[SP_bs][v]) // Set the current vertex to the current predecessor, and the predecessor to one level up
				{
					double ec = get(boost::edge_weight_t(), instance_graph, boost::edge(u, v, instance_graph).first);
					double goodput_this_edge = 1 - pow(ec, retransmission_Mr[x]);
					goodput_this_sensor = goodput_this_sensor * goodput_this_edge;
					// calculate delay
					double ETr = (1 - pow(ec, retransmission_Mr[x])) / (1 - ec);
					double lambada = delay_p / ETr;
					double ETr2 = (1 - (2 * retransmission_Mr[x] - 1)*pow(ec, retransmission_Mr[x])) / (1 - ec) +
						2 * ec*(1 - pow(ec, retransmission_Mr[x] - 1)) / pow(1 - ec, 2);
					double T_soj = lambada * ETr2 / 2 / (1 - delay_p) + 1 / 2 + ETr;
					delay_this_sensor = delay_this_sensor + T_soj;
					if (terminal[u] == 1 && leaf_terminal[u] == 0) { // u is bs
						break;
					}
				}
				average_goodput[x] = average_goodput[x] + goodput_this_sensor;
				average_delay[x] = average_delay[x] + delay_this_sensor;
			}

		}
	}


	average_efficiency = average_efficiency / sensor_num;
	net_lifetime = sensor_transmission_times * average_efficiency;

	for (int x = 0; x < Mr_num; x++) {
		average_goodput[x] = average_goodput[x] / sensor_num;
		average_delay[x] = average_delay[x] / sensor_num;
	}
	goodput = average_goodput;
	delay = average_delay;


}
#pragma endregion WSN_performance_SP




/*experiments*/

#pragma region 
void CCG_grid_PA_experiment_STPsolution_large_fastMST(int start_num, int end_num) {


	int B_target, R_target, S_target, min_relay_nw = 100, max_relay_nw = 500,
		Euclidean_x_max, Euclidean_y_max;
	std::vector<int> retransmission_Mr = { 10,40,70,100 };
	double sensitivity_rth, P_S = 1e-7, P_R = 4e-7, reference_distance = 1, b_a, delay_p = 0.1;
	double valid_ratio = 0;
	int V_SMT_upperbound = 25;
	int iteration_times = 300;

	int best_solution_K;

	int K_1 = 0;;// PSTA parameters
	int K_2 = 500;// PSTA parameters
	int K_3 = 100; // PSTA parameters
	int K_4 = 0; // PSTA parameters

	int ins_ID = (start_num - 1) * iteration_times;


	for (int num = start_num; num <= end_num; num++) {

		string save_name = "CCG_grid_PA_experiment_STPsolution_large" + to_string(num) + ".csv";
		ofstream outputFile;
		outputFile.precision(10);
		outputFile.setf(ios::fixed);
		outputFile.setf(ios::showpoint);
		outputFile.open(save_name);
		outputFile << "R,b/a,rth,avg_EA_time(ms),avg_PA1_time,avg_PA2_time,avg_PA3_time,avg_PA4_time,avg_1999_time,";
		outputFile << "avg_EA_cost,avg_PA1_cost,avg_PA2_cost,avg_PA3_cost,avg_PA4_cost,avg_1999_cost,";
		outputFile << "R,b/a,rth,Mr1,Mr2,Mr3,Mr4,avg_PSTA_time(ms),avg_Guha_16103_time,avg_OSRP_2016_time,avg_RRPL_2017_time,";
		outputFile << "avg_PSTA_relay_cost,avg_Guha_16103_relay_cost,avg_OSRP_2016_relay_cost,avg_RRPL_2017_relay_cost,";

		outputFile << "avg_PSTA_netlifetime_sum_p,avg_Guha_16103_netlifetime_sum_p,avg_OSRP_2016_netlifetime_sum_p,avg_RRPL_2017_netlifetime_sum_p,";
		outputFile << "avg_PSTA_goodput1_sum_p,avg_Guha_16103_goodput1_sum_p,avg_OSRP_2016_goodput1_sum_p,avg_RRPL_2017_goodput1_sum_p,";
		outputFile << "avg_PSTA_goodput2_sum_p,avg_Guha_16103_goodput2_sum_p,avg_OSRP_2016_goodput2_sum_p,avg_RRPL_2017_goodput2_sum_p,";
		outputFile << "avg_PSTA_goodput3_sum_p,avg_Guha_16103_goodput3_sum_p,avg_OSRP_2016_goodput3_sum_p,avg_RRPL_2017_goodput3_sum_p,";
		outputFile << "avg_PSTA_goodput4_sum_p,avg_Guha_16103_goodput4_sum_p,avg_OSRP_2016_goodput4_sum_p,avg_RRPL_2017_goodput4_sum_p,";
		outputFile << "avg_PSTA_delay1_sum_p,avg_Guha_16103_delay1_sum_p,avg_OSRP_2016_delay1_sum_p,avg_RRPL_2017_delay1_sum_p,";
		outputFile << "avg_PSTA_delay2_sum_p,avg_Guha_16103_delay2_sum_p,avg_OSRP_2016_delay2_sum_p,avg_RRPL_2017_delay2_sum_p,";
		outputFile << "avg_PSTA_delay3_sum_p,avg_Guha_16103_delay3_sum_p,avg_OSRP_2016_delay3_sum_p,avg_RRPL_2017_delay3_sum_p,";
		outputFile << "avg_PSTA_delay4_sum_p,avg_Guha_16103_delay4_sum_p,avg_OSRP_2016_delay4_sum_p,avg_RRPL_2017_delay4_sum_p,";


		outputFile << "avg_PSTA_netlifetime_routing_tree,avg_Guha_16103_netlifetime_routing_tree,avg_OSRP_2016_netlifetime_routing_tree,avg_RRPL_2017_netlifetime_routing_tree,";
		outputFile << "avg_PSTA_goodput1_routing_tree,avg_Guha_16103_goodput1_routing_tree,avg_OSRP_2016_goodput1_routing_tree,avg_RRPL_2017_goodput1_routing_tree,";
		outputFile << "avg_PSTA_goodput2_routing_tree,avg_Guha_16103_goodput2_routing_tree,avg_OSRP_2016_goodput2_routing_tree,avg_RRPL_2017_goodput2_routing_tree,";
		outputFile << "avg_PSTA_goodput3_routing_tree,avg_Guha_16103_goodput3_routing_tree,avg_OSRP_2016_goodput3_routing_tree,avg_RRPL_2017_goodput3_routing_tree,";
		outputFile << "avg_PSTA_goodput4_routing_tree,avg_Guha_16103_goodput4_routing_tree,avg_OSRP_2016_goodput4_routing_tree,avg_RRPL_2017_goodput4_routing_tree,";
		outputFile << "avg_PSTA_delay1_routing_tree,avg_Guha_16103_delay1_routing_tree,avg_OSRP_2016_delay1_routing_tree,avg_RRPL_2017_delay1_routing_tree,";
		outputFile << "avg_PSTA_delay2_routing_tree,avg_Guha_16103_delay2_routing_tree,avg_OSRP_2016_delay2_routing_tree,avg_RRPL_2017_delay2_routing_tree,";
		outputFile << "avg_PSTA_delay3_routing_tree,avg_Guha_16103_delay3_routing_tree,avg_OSRP_2016_delay3_routing_tree,avg_RRPL_2017_delay3_routing_tree,";
		outputFile << "avg_PSTA_delay4_routing_tree,avg_Guha_16103_delay4_routing_tree,avg_OSRP_2016_delay4_routing_tree,avg_RRPL_2017_delay4_routing_tree,";



		outputFile << "avg_PSTA_netlifetime_SP,avg_Guha_16103_netlifetime_SP,avg_OSRP_2016_netlifetime_SP,avg_RRPL_2017_netlifetime_SP,";
		outputFile << "avg_PSTA_goodput1_SP,avg_Guha_16103_goodput1_SP,avg_OSRP_2016_goodput1_SP,avg_RRPL_2017_goodput1_SP,";
		outputFile << "avg_PSTA_goodput2_SP,avg_Guha_16103_goodput2_SP,avg_OSRP_2016_goodput2_SP,avg_RRPL_2017_goodput2_SP,";
		outputFile << "avg_PSTA_goodput3_SP,avg_Guha_16103_goodput3_SP,avg_OSRP_2016_goodput3_SP,avg_RRPL_2017_goodput3_SP,";
		outputFile << "avg_PSTA_goodput4_SP,avg_Guha_16103_goodput4_SP,avg_OSRP_2016_goodput4_SP,avg_RRPL_2017_goodput4_SP,";
		outputFile << "avg_PSTA_delay1_SP,avg_Guha_16103_delay1_SP,avg_OSRP_2016_delay1_SP,avg_RRPL_2017_delay1_SP,";
		outputFile << "avg_PSTA_delay2_SP,avg_Guha_16103_delay2_SP,avg_OSRP_2016_delay2_SP,avg_RRPL_2017_delay2_SP,";
		outputFile << "avg_PSTA_delay3_SP,avg_Guha_16103_delay3_SP,avg_OSRP_2016_delay3_SP,avg_RRPL_2017_delay3_SP,";
		outputFile << "avg_PSTA_delay4_SP,avg_Guha_16103_delay4_SP,avg_OSRP_2016_delay4_SP,avg_RRPL_2017_delay4_SP,S,B,";

		outputFile << "PSTA2_average_route_length,PSTA2_average_route_p" << endl;


		Euclidean_x_max = sqrt(1500); Euclidean_y_max = sqrt(1500);


		if (num == 11) {
			S_target = 90;
			Euclidean_x_max = sqrt(1500 * 0.9); Euclidean_y_max = sqrt(1500 * 0.9);
		}
		else if (num == 12) {
			S_target = 95;
			Euclidean_x_max = sqrt(1500 * 0.95); Euclidean_y_max = sqrt(1500 * 0.95);
		}
		else if (num == 13) {
			S_target = 105;
			Euclidean_x_max = sqrt(1500 * 1.05); Euclidean_y_max = sqrt(1500 * 1.05);
		}
		else {
			S_target = 100;
		}

		if (num == 14) {
			B_target = 4;
		}
		else if (num == 15) {
			B_target = 6;
		}
		else if (num == 16) {
			B_target = 8;
		}
		else {
			B_target = 2;
		}


		// vary R_target
		if (num == 1) {
			R_target = 25;
		}
		else if (num == 3) {
			R_target = 30;
		}
		else if (num == 4) {
			R_target = 35;
		}
		else {
			R_target = 20;
		}




		// vary b_a
		if (num == 5) {
			b_a = 1;
		}
		else if (num == 6) {
			b_a = 50;
		}
		else if (num == 7) {
			b_a = 100;
		}
		else {
			b_a = 150;
		}


		// vary sensitivity_rth
		if (num == 8) {
			sensitivity_rth = 8e-10;
		}
		else if (num == 9) {
			sensitivity_rth = 10e-10;
		}
		else if (num == 10) {
			sensitivity_rth = 12e-10;
		}
		else {
			sensitivity_rth = 6e-10;
		}



		int iteration_ID = 0;
		while (iteration_ID < iteration_times) {


			std::vector<int> terminal, leaf_terminal;
			graph instance_graph, distance_graph;

			int generate_new_graph = 1;
			if (generate_new_graph == 1) {

				ins_ID++;

				instance_graph = generate_CCG_grid_multipleBS
				(distance_graph, terminal, leaf_terminal, B_target, R_target, S_target, min_relay_nw, max_relay_nw,
					sensitivity_rth, P_S, P_R, reference_distance, b_a, Euclidean_x_max, Euclidean_y_max, valid_ratio);

				//save_NWPFSTP_graph_with_leafterminals("YahuiNWSTPins_" + to_string(ins_ID), instance_graph, terminal, leaf_terminal);
				//save_NWPFSTP_graph_with_leafterminals_Daniel("NWSTPins_" + to_string(ins_ID), instance_graph, terminal, leaf_terminal);

				cout << "num_vertices(instance_graph): " << num_vertices(instance_graph)
					<< " num_edges(instance_graph): " << num_edges(instance_graph) << endl;
			}
			else {
				ins_ID++;
				instance_graph = read_NWPFSTP_data_with_leafterminals("YahuiNWSTPins_" + to_string(ins_ID) + ".stp", terminal, leaf_terminal);
			}

			//cout << "intance generated!" << endl;
			//getchar();


			iteration_ID++; // valid instance

			//cout << "1" << endl;


			auto begin_time2 = std::chrono::high_resolution_clock::now(); // start time
			graph PSTA1_solution = PSTA_NWPTSTP_CCG_fastMST(instance_graph, terminal, leaf_terminal, K_1, best_solution_K);
			auto end_time2 = std::chrono::high_resolution_clock::now();
			double PSTA1_time = 1 * std::chrono::duration_cast<std::chrono::nanoseconds>(end_time2 - begin_time2).count(); // Nanosecond

			//cout << "2" << endl;

			auto begin_time4 = std::chrono::high_resolution_clock::now(); // start time
			graph PSTA2_solution = PSTA_NWPTSTP_CCG_fastMST(instance_graph, terminal, leaf_terminal, K_2, best_solution_K);
			auto end_time4 = std::chrono::high_resolution_clock::now();
			double PSTA2_time = 1 * std::chrono::duration_cast<std::chrono::nanoseconds>(end_time4 - begin_time4).count(); // Nanosecond

			//cout << "3" << endl;

			auto begin_time5 = std::chrono::high_resolution_clock::now(); // start time
			graph PSTA3_solution = PSTA_NWPTSTP_CCG_fastMST(instance_graph, terminal, leaf_terminal, K_3, best_solution_K);
			auto end_time5 = std::chrono::high_resolution_clock::now();
			double PSTA3_time = 1 * std::chrono::duration_cast<std::chrono::nanoseconds>(end_time5 - begin_time5).count(); // Nanosecond

			//cout << "4" << endl;

			auto begin_time6 = std::chrono::high_resolution_clock::now(); // start time
			graph PSTA4_solution = PSTA_NWPTSTP_CCG_fastMST(instance_graph, terminal, leaf_terminal, K_4, best_solution_K);
			auto end_time6 = std::chrono::high_resolution_clock::now();
			double PSTA4_time = 1 * std::chrono::duration_cast<std::chrono::nanoseconds>(end_time6 - begin_time6).count(); // Nanosecond

			//cout << "5" << endl;

			auto begin_time3 = std::chrono::high_resolution_clock::now(); // start time
			graph Guha_16103_solution = Guha_16103(instance_graph, terminal, leaf_terminal);
			auto end_time3 = std::chrono::high_resolution_clock::now();
			double Guha_16103_time = std::chrono::duration_cast<std::chrono::nanoseconds>(end_time3 - begin_time3).count(); // Nanosecond

			//cout << "6" << endl;	

			auto begin_time7 = std::chrono::high_resolution_clock::now(); // start time
			graph RRPL_solution = RRPL_2017_outage_paper_algorithm_multiple_bs_sensor_can_connect_bs(instance_graph, terminal, leaf_terminal);
			auto end_time7 = std::chrono::high_resolution_clock::now();
			double RRPL_time = std::chrono::duration_cast<std::chrono::nanoseconds>(end_time7 - begin_time7).count(); // Nanosecond


			//cout << "7" << endl;

			auto begin_time8 = std::chrono::high_resolution_clock::now(); // start time
			graph OSRP_solution = OSRP_2016_IEEEletter_paper_algorithm_sensor_can_connect_bs(instance_graph, terminal, leaf_terminal);
			auto end_time8 = std::chrono::high_resolution_clock::now();
			double OSRP_time = std::chrono::duration_cast<std::chrono::nanoseconds>(end_time8 - begin_time8).count(); // Nanosecond


			//cout << "8" << endl;

			double PSTA1_cost = net_cost_KleinNWSTP(PSTA1_solution, terminal);
			double PSTA2_cost = net_cost_KleinNWSTP(PSTA2_solution, terminal);
			double PSTA3_cost = net_cost_KleinNWSTP(PSTA3_solution, terminal);
			double PSTA4_cost = net_cost_KleinNWSTP(PSTA4_solution, terminal);
			double Guha_16103_cost = net_cost_KleinNWSTP(Guha_16103_solution, terminal);
			double optimal_cost = 0;

			double PSTA2_relay_cost = relay_cost(num_vertices(instance_graph), PSTA2_solution, b_a, terminal, min_relay_nw, max_relay_nw);
			double Guha_16103_relay_cost = relay_cost(num_vertices(instance_graph), Guha_16103_solution, b_a, terminal, min_relay_nw, max_relay_nw);
			double RRPL_relay_cost = relay_cost(num_vertices(instance_graph), RRPL_solution, b_a, terminal, min_relay_nw, max_relay_nw);
			double OSRP_relay_cost = relay_cost(num_vertices(instance_graph), OSRP_solution, b_a, terminal, min_relay_nw, max_relay_nw);



			/*sum_p*/
			double PSTA2_net_lifetime_sum_p;
			std::vector<double> PSTA2_delay_sum_p(4);
			std::vector<double> PSTA2_goodput_sum_p(4);
			double PSTA2_average_route_length = 0;
			double PSTA2_average_route_p = 0;
			WSN_performance_min_sum_of_p(instance_graph, PSTA2_solution, terminal, leaf_terminal, delay_p,
				retransmission_Mr, PSTA2_net_lifetime_sum_p, PSTA2_delay_sum_p, PSTA2_goodput_sum_p, 
				PSTA2_average_route_length, PSTA2_average_route_p);
			double Guha_16103_net_lifetime_sum_p;
			std::vector<double> Guha_16103_delay_sum_p(4);
			std::vector<double> Guha_16103_goodput_sum_p(4);
			double Guha_average_route_length = 0;
			double Guha_average_route_p = 0;
			WSN_performance_min_sum_of_p(instance_graph, Guha_16103_solution, terminal, leaf_terminal, delay_p,
				retransmission_Mr, Guha_16103_net_lifetime_sum_p, Guha_16103_delay_sum_p, Guha_16103_goodput_sum_p,
				Guha_average_route_length, Guha_average_route_p);
			double RRPL_net_lifetime_sum_p;
			std::vector<double> RRPL_delay_sum_p(4);
			std::vector<double> RRPL_goodput_sum_p(4);
			double RRPL_average_route_length = 0;
			double RRPL_average_route_p = 0;
			WSN_performance_min_sum_of_p(instance_graph, RRPL_solution, terminal, leaf_terminal, delay_p,
				retransmission_Mr, RRPL_net_lifetime_sum_p, RRPL_delay_sum_p, RRPL_goodput_sum_p,
				RRPL_average_route_length, RRPL_average_route_p);
			double OSRP_net_lifetime_sum_p;
			std::vector<double> OSRP_delay_sum_p(4);
			std::vector<double> OSRP_goodput_sum_p(4);
			double OSRP_average_route_length = 0;
			double OSRP_average_route_p = 0;
			WSN_performance_min_sum_of_p(instance_graph, OSRP_solution, terminal, leaf_terminal, delay_p,
				retransmission_Mr, OSRP_net_lifetime_sum_p, OSRP_delay_sum_p, OSRP_goodput_sum_p,
				OSRP_average_route_length, OSRP_average_route_p);



			/*routing_tree*/
			double PSTA2_net_lifetime_routing_tree;
			std::vector<double> PSTA2_delay_routing_tree(4);
			std::vector<double> PSTA2_goodput_routing_tree(4);
			WSN_performance_routing_tree(instance_graph, PSTA2_solution, terminal, leaf_terminal, delay_p,
				retransmission_Mr, PSTA2_net_lifetime_routing_tree, PSTA2_delay_routing_tree, PSTA2_goodput_routing_tree);
			double Guha_16103_net_lifetime_routing_tree;
			std::vector<double> Guha_16103_delay_routing_tree(4);
			std::vector<double> Guha_16103_goodput_routing_tree(4);
			WSN_performance_routing_tree(instance_graph, Guha_16103_solution, terminal, leaf_terminal, delay_p,
				retransmission_Mr, Guha_16103_net_lifetime_routing_tree, Guha_16103_delay_routing_tree, Guha_16103_goodput_routing_tree);
			double RRPL_net_lifetime_routing_tree;
			std::vector<double> RRPL_delay_routing_tree(4);
			std::vector<double> RRPL_goodput_routing_tree(4);
			WSN_performance_routing_tree(instance_graph, RRPL_solution, terminal, leaf_terminal, delay_p,
				retransmission_Mr, RRPL_net_lifetime_routing_tree, RRPL_delay_routing_tree, RRPL_goodput_routing_tree);
			double OSRP_net_lifetime_routing_tree;
			std::vector<double> OSRP_delay_routing_tree(4);
			std::vector<double> OSRP_goodput_routing_tree(4);
			WSN_performance_routing_tree(instance_graph, OSRP_solution, terminal, leaf_terminal, delay_p,
				retransmission_Mr, OSRP_net_lifetime_routing_tree, OSRP_delay_routing_tree, OSRP_goodput_routing_tree);



			/*SP*/
			double PSTA2_net_lifetime_SP;
			std::vector<double> PSTA2_delay_SP(4);
			std::vector<double> PSTA2_goodput_SP(4);
			WSN_performance_SP(instance_graph, distance_graph, PSTA2_solution, terminal, leaf_terminal, delay_p,
				retransmission_Mr, PSTA2_net_lifetime_SP, PSTA2_delay_SP, PSTA2_goodput_SP);
			double Guha_16103_net_lifetime_SP;
			std::vector<double> Guha_16103_delay_SP(4);
			std::vector<double> Guha_16103_goodput_SP(4);
			WSN_performance_SP(instance_graph, distance_graph, Guha_16103_solution, terminal, leaf_terminal, delay_p,
				retransmission_Mr, Guha_16103_net_lifetime_SP, Guha_16103_delay_SP, Guha_16103_goodput_SP);
			double RRPL_net_lifetime_SP;
			std::vector<double> RRPL_delay_SP(4);
			std::vector<double> RRPL_goodput_SP(4);
			WSN_performance_SP(instance_graph, distance_graph, RRPL_solution, terminal, leaf_terminal, delay_p,
				retransmission_Mr, RRPL_net_lifetime_SP, RRPL_delay_SP, RRPL_goodput_SP);
			double OSRP_net_lifetime_SP;
			std::vector<double> OSRP_delay_SP(4);
			std::vector<double> OSRP_goodput_SP(4);
			WSN_performance_SP(instance_graph, distance_graph, OSRP_solution, terminal, leaf_terminal, delay_p,
				retransmission_Mr, OSRP_net_lifetime_SP, OSRP_delay_SP, OSRP_goodput_SP);





			outputFile << R_target << "," << b_a << "," << sensitivity_rth << "," <<
				0 / 1e6 << "," << PSTA1_time / 1e6 << "," << PSTA2_time / 1e6 << ","
				<< PSTA3_time / 1e6 << "," << PSTA4_time / 1e6 << ","
				<< Guha_16103_time / 1e6 << "," <<
				optimal_cost << "," << PSTA1_cost << "," << PSTA2_cost << "," <<
				PSTA3_cost << "," << PSTA4_cost << "," <<
				Guha_16103_cost << "," <<
				R_target << "," << b_a << "," << sensitivity_rth << "," << retransmission_Mr[0] << "," <<
				retransmission_Mr[1] << "," << retransmission_Mr[2] << "," << retransmission_Mr[3] << "," <<
				PSTA2_time / 1e6 << "," << Guha_16103_time / 1e6 << ","
				<< OSRP_time / 1e6 << "," << RRPL_time / 1e6 << "," <<
				PSTA2_relay_cost << "," << Guha_16103_relay_cost << "," <<
				OSRP_relay_cost << "," << RRPL_relay_cost << "," <<

				PSTA2_net_lifetime_sum_p << "," << Guha_16103_net_lifetime_sum_p << "," <<
				OSRP_net_lifetime_sum_p << "," << RRPL_net_lifetime_sum_p << "," <<
				PSTA2_goodput_sum_p[0] << "," << Guha_16103_goodput_sum_p[0] << "," <<
				OSRP_goodput_sum_p[0] << "," << RRPL_goodput_sum_p[0] << "," <<
				PSTA2_goodput_sum_p[1] << "," << Guha_16103_goodput_sum_p[1] << "," <<
				OSRP_goodput_sum_p[1] << "," << RRPL_goodput_sum_p[1] << "," <<
				PSTA2_goodput_sum_p[2] << "," << Guha_16103_goodput_sum_p[2] << "," <<
				OSRP_goodput_sum_p[2] << "," << RRPL_goodput_sum_p[2] << "," <<
				PSTA2_goodput_sum_p[3] << "," << Guha_16103_goodput_sum_p[3] << "," <<
				OSRP_goodput_sum_p[3] << "," << RRPL_goodput_sum_p[3] << "," <<
				PSTA2_delay_sum_p[0] << "," << Guha_16103_delay_sum_p[0] << "," <<
				OSRP_delay_sum_p[0] << "," << RRPL_delay_sum_p[0] << "," <<
				PSTA2_delay_sum_p[1] << "," << Guha_16103_delay_sum_p[1] << "," <<
				OSRP_delay_sum_p[1] << "," << RRPL_delay_sum_p[1] << "," <<
				PSTA2_delay_sum_p[2] << "," << Guha_16103_delay_sum_p[2] << "," <<
				OSRP_delay_sum_p[2] << "," << RRPL_delay_sum_p[2] << "," <<
				PSTA2_delay_sum_p[3] << "," << Guha_16103_delay_sum_p[3] << "," <<
				OSRP_delay_sum_p[3] << "," << RRPL_delay_sum_p[3] << "," << 


			    PSTA2_net_lifetime_routing_tree << "," << Guha_16103_net_lifetime_routing_tree << "," <<
				OSRP_net_lifetime_routing_tree << "," << RRPL_net_lifetime_routing_tree << "," <<
				PSTA2_goodput_routing_tree[0] << "," << Guha_16103_goodput_routing_tree[0] << "," <<
				OSRP_goodput_routing_tree[0] << "," << RRPL_goodput_routing_tree[0] << "," <<
				PSTA2_goodput_routing_tree[1] << "," << Guha_16103_goodput_routing_tree[1] << "," <<
				OSRP_goodput_routing_tree[1] << "," << RRPL_goodput_routing_tree[1] << "," <<
				PSTA2_goodput_routing_tree[2] << "," << Guha_16103_goodput_routing_tree[2] << "," <<
				OSRP_goodput_routing_tree[2] << "," << RRPL_goodput_routing_tree[2] << "," <<
				PSTA2_goodput_routing_tree[3] << "," << Guha_16103_goodput_routing_tree[3] << "," <<
				OSRP_goodput_routing_tree[3] << "," << RRPL_goodput_routing_tree[3] << "," <<
				PSTA2_delay_routing_tree[0] << "," << Guha_16103_delay_routing_tree[0] << "," <<
				OSRP_delay_routing_tree[0] << "," << RRPL_delay_routing_tree[0] << "," <<
				PSTA2_delay_routing_tree[1] << "," << Guha_16103_delay_routing_tree[1] << "," <<
				OSRP_delay_routing_tree[1] << "," << RRPL_delay_routing_tree[1] << "," <<
				PSTA2_delay_routing_tree[2] << "," << Guha_16103_delay_routing_tree[2] << "," <<
				OSRP_delay_routing_tree[2] << "," << RRPL_delay_routing_tree[2] << "," <<
				PSTA2_delay_routing_tree[3] << "," << Guha_16103_delay_routing_tree[3] << "," <<
				OSRP_delay_routing_tree[3] << "," << RRPL_delay_routing_tree[3] << "," << 


			    PSTA2_net_lifetime_SP << "," << Guha_16103_net_lifetime_SP << "," <<
				OSRP_net_lifetime_SP << "," << RRPL_net_lifetime_SP << "," <<
				PSTA2_goodput_SP[0] << "," << Guha_16103_goodput_SP[0] << "," <<
				OSRP_goodput_SP[0] << "," << RRPL_goodput_SP[0] << "," <<
				PSTA2_goodput_SP[1] << "," << Guha_16103_goodput_SP[1] << "," <<
				OSRP_goodput_SP[1] << "," << RRPL_goodput_SP[1] << "," <<
				PSTA2_goodput_SP[2] << "," << Guha_16103_goodput_SP[2] << "," <<
				OSRP_goodput_SP[2] << "," << RRPL_goodput_SP[2] << "," <<
				PSTA2_goodput_SP[3] << "," << Guha_16103_goodput_SP[3] << "," <<
				OSRP_goodput_SP[3] << "," << RRPL_goodput_SP[3] << "," <<
				PSTA2_delay_SP[0] << "," << Guha_16103_delay_SP[0] << "," <<
				OSRP_delay_SP[0] << "," << RRPL_delay_SP[0] << "," <<
				PSTA2_delay_SP[1] << "," << Guha_16103_delay_SP[1] << "," <<
				OSRP_delay_SP[1] << "," << RRPL_delay_SP[1] << "," <<
				PSTA2_delay_SP[2] << "," << Guha_16103_delay_SP[2] << "," <<
				OSRP_delay_SP[2] << "," << RRPL_delay_SP[2] << "," <<
				PSTA2_delay_SP[3] << "," << Guha_16103_delay_SP[3] << "," <<
				OSRP_delay_SP[3] << "," << RRPL_delay_SP[3] << "," << S_target << "," << B_target << "," <<

				PSTA2_average_route_length << "," << PSTA2_average_route_p << endl;




		}

	}



}
#pragma endregion CCG_grid_PA_experiment_STPsolution_large_fastMST

#pragma region 
void CCG_grid_PA_experiment_STPsolution_very_large_fastMST() {


	int B_target, R_target, S_target, min_relay_nw = 100, max_relay_nw = 500,
		Euclidean_x_max, Euclidean_y_max;
	double sensitivity_rth, P_S = 1e-7, P_R = 4e-7, reference_distance = 1, b_a, delay_p = 0.1;
	double valid_ratio = 0;
	int V_SMT_upperbound = 25;
	int iteration_times = 300;

	int best_solution_K;

	int K_1 = 0;// PSTA parameters
	int K_2 = 500;// PSTA parameters
	int K_3 = 100;// PSTA parameters
	int K_4 = 0; // PSTA parameters


	int ins_ID = iteration_times * 16;


	for (int num = 1; num <= 4; num++) {

		string save_name = "CCG_grid_PA_experiment_STPsolution_very_large" + to_string(num) + ".csv";
		ofstream outputFile;
		outputFile.precision(10);
		outputFile.setf(ios::fixed);
		outputFile.setf(ios::showpoint);
		outputFile.open(save_name);
		outputFile << "R,b/a,rth,avg_EA_time(ms),avg_PA1_time,avg_PA2_time,avg_PA3_time,avg_PA4_time,avg_1999_time,";
		outputFile << "avg_EA_cost,avg_PA1_cost,avg_PA2_cost,avg_PA3_cost,avg_PA4_cost,avg_1999_cost,S,B" << endl;


		B_target = 10;
		R_target = 100;
		Euclidean_x_max = sqrt(6000); Euclidean_y_max = sqrt(6000);

		// vary R_target
		if (num == 1) {
			S_target = 400;
			Euclidean_x_max = sqrt(6000 * 4 / 5); Euclidean_y_max = sqrt(6000 * 4 / 5);
		}
		else if (num == 3) {
			S_target = 600;
			Euclidean_x_max = sqrt(6000 * 6 / 5); Euclidean_y_max = sqrt(6000 * 6 / 5);
		}
		else if (num == 4) {
			S_target = 700;
			Euclidean_x_max = sqrt(6000 * 7 / 5); Euclidean_y_max = sqrt(6000 * 7 / 5);
		}
		else {
			S_target = 500;
		}

		b_a = 150;
		sensitivity_rth = 6e-10;



		int iteration_ID = 0;
		while (iteration_ID < iteration_times) {


			std::vector<int> terminal, leaf_terminal;
			graph instance_graph, distance_graph;

			int generate_new_graph = 1;
			if (generate_new_graph == 1) {

				ins_ID++;


				instance_graph = generate_CCG_grid_multipleBS
				(distance_graph, terminal, leaf_terminal, B_target, R_target, S_target, min_relay_nw, max_relay_nw,
					sensitivity_rth, P_S, P_R, reference_distance, b_a, Euclidean_x_max, Euclidean_y_max, valid_ratio);

				//save_NWPFSTP_graph_with_leafterminals("YahuiNWSTPins_" + to_string(ins_ID), instance_graph, terminal, leaf_terminal);
				//save_NWPFSTP_graph_with_leafterminals_Daniel("NWSTPins_" + to_string(ins_ID), instance_graph, terminal, leaf_terminal);

				cout << "num_vertices(instance_graph): " << num_vertices(instance_graph)
					<< " num_edges(instance_graph): " << num_edges(instance_graph) << endl;
			}
			else {
				ins_ID++;
				instance_graph = read_NWPFSTP_data_with_leafterminals("YahuiNWSTPins_" + to_string(ins_ID) + ".stp", terminal, leaf_terminal);
			}

			//cout << "intance generated!" << endl;
			//getchar();


			iteration_ID++; // valid instance

			auto begin_time4 = std::chrono::high_resolution_clock::now(); // start time
			graph PSTA2_solution = PSTA_NWPTSTP_CCG_fastMST(instance_graph, terminal, leaf_terminal, K_2, best_solution_K);
			auto end_time4 = std::chrono::high_resolution_clock::now();
			double PSTA2_time = 1 * std::chrono::duration_cast<std::chrono::nanoseconds>(end_time4 - begin_time4).count(); // Nanosecond

																														   //cout << "3" << endl;

			auto begin_time5 = std::chrono::high_resolution_clock::now(); // start time
			graph PSTA3_solution = PSTA_NWPTSTP_CCG_fastMST(instance_graph, terminal, leaf_terminal, K_3, best_solution_K);
			auto end_time5 = std::chrono::high_resolution_clock::now();
			double PSTA3_time = 1 * std::chrono::duration_cast<std::chrono::nanoseconds>(end_time5 - begin_time5).count(); // Nanosecond


			double PSTA1_cost = 0;
			double PSTA2_cost = net_cost_KleinNWSTP(PSTA2_solution, terminal);
			double PSTA3_cost = net_cost_KleinNWSTP(PSTA3_solution, terminal);
			double PSTA4_cost = 0;
			double Guha_16103_cost = 0;
			double optimal_cost = 0;

			outputFile << R_target << "," << b_a << "," << sensitivity_rth << "," <<
				0 / 1e6 << "," << 0 / 1e6 << "," << PSTA2_time / 1e6 << ","
				<< PSTA3_time / 1e6 << "," << 0 / 1e6 << ","
				<< 0 / 1e6 << "," <<
				optimal_cost << "," << PSTA1_cost << "," << PSTA2_cost << "," <<
				PSTA3_cost << "," << PSTA4_cost << "," <<
				Guha_16103_cost << "," <<
				S_target << "," <<
				B_target << endl;

			//cout << "intance solved!" << endl;
			//getchar();


		}

	}



}
#pragma endregion CCG_grid_PA_experiment_STPsolution_very_large_fastMST

#pragma region 
void varying_k(int ID, double iteration_times) {

	/*parameters*/
	int B_target, R_target, S_target, min_relay_nw = 100, max_relay_nw = 500,
		Euclidean_x_max, Euclidean_y_max;
	double sensitivity_rth, P_S = 1e-7, P_R = 4e-7, reference_distance = 1, b_a, delay_p = 0.1;
	double valid_ratio = 0;
	int best_solution_K;
	int k_min = 1, k_max = 500;

	/*random_k_preparation*/
	std::time_t now = std::time(0);
	boost::random::mt19937 gen{ static_cast<std::uint32_t>(now) };
	boost::random::uniform_int_distribution<> dist{ k_min, k_max };

	/*parameters*/
	if (ID == 1) { // base
		B_target = 2;
		R_target = 20;
		S_target = 100;
		b_a = 150;
		sensitivity_rth = 6e-10;
		Euclidean_x_max = sqrt(1500); Euclidean_y_max = sqrt(1500);
	}
	else if (ID == 2) { // small b_a
		B_target = 2;
		R_target = 20;
		S_target = 100;
		b_a = 50;
		sensitivity_rth = 6e-10;
		Euclidean_x_max = sqrt(1500); Euclidean_y_max = sqrt(1500);
	}
	else if (ID == 3) { // large B_target
		B_target = 8;
		R_target = 20;
		S_target = 100;
		b_a = 150;
		sensitivity_rth = 6e-10;
		Euclidean_x_max = sqrt(1500); Euclidean_y_max = sqrt(1500);
	}
	else if (ID == 4) { // small S_target
		B_target = 2;
		R_target = 20;
		S_target = 90;
		b_a = 150;
		sensitivity_rth = 6e-10;
		Euclidean_x_max = sqrt(1500 * 0.9); Euclidean_y_max = sqrt(1500 * 0.9);
	}
	else if (ID == 5) { // large R_target
		B_target = 2;
		R_target = 35;
		S_target = 100;
		b_a = 150;
		sensitivity_rth = 6e-10;
		Euclidean_x_max = sqrt(1500); Euclidean_y_max = sqrt(1500);
	}
	else if (ID == 6) { // large sensitivity_rth
		B_target = 2;
		R_target = 20;
		S_target = 100;
		b_a = 150;
		sensitivity_rth = 12e-10;
		Euclidean_x_max = sqrt(1500); Euclidean_y_max = sqrt(1500);
	}



	string save_name = "varying_k_" + to_string(ID) + ".csv";
	ofstream outputFile;
	outputFile.precision(10);
	outputFile.setf(ios::fixed);
	outputFile.setf(ios::showpoint);
	outputFile.open(save_name);
	outputFile << "random_k,algorithm,solution_cost" << endl;


	for (int itera = 0; itera < iteration_times; itera++) {

		cout << "instance_" << ID << "_" << itera << endl;

		/*random_K*/
		int random_k = dist(gen);

		/*generate instance*/
		std::vector<int> terminal, leaf_terminal;
		graph instance_graph, distance_graph;
		instance_graph = generate_CCG_grid_multipleBS
		(distance_graph, terminal, leaf_terminal, B_target, R_target, S_target, min_relay_nw, max_relay_nw,
			sensitivity_rth, P_S, P_R, reference_distance, b_a, Euclidean_x_max, Euclidean_y_max, valid_ratio);
		

		graph PSTA_solution = PSTA_NWPTSTP_CCG_fastMST(instance_graph, terminal, leaf_terminal, random_k, best_solution_K);
		graph Guha_16103_solution = Guha_16103(instance_graph, terminal, leaf_terminal);

		double PSTA_cost = net_cost_KleinNWSTP(PSTA_solution, terminal);
		double Guha_16103_cost = net_cost_KleinNWSTP(Guha_16103_solution, terminal);

		outputFile << random_k << ",PSTA," << PSTA_cost << endl;
		outputFile << random_k << ",GKA," << Guha_16103_cost << endl;

	}

	outputFile.close();

}
#pragma endregion varying_k

#pragma region 
void parallel_varying_k() {

	int iteration_times = 1000;

	boost::thread_group threads;
	for (int ID = 1; ID <= 6; ID++) {
		boost::thread* t = new boost::thread{ varying_k, ID, iteration_times };
		threads.add_thread(t);
	}
	threads.join_all();

}
#pragma endregion parallel_varying_k

#pragma region 
void non_parallel_experiments() {

	CCG_grid_PA_experiment_STPsolution_large_fastMST(1, 16);

	CCG_grid_PA_experiment_STPsolution_very_large_fastMST();

}
#pragma endregion non_parallel_experiments

#pragma region 
void parallel_experiments() {

	boost::thread_group threads;
	for (int i = 1; i <= 16; i++) {
		boost::thread* t = new boost::thread{ CCG_grid_PA_experiment_STPsolution_large_fastMST, i, i };
		threads.add_thread(t);
	}
	boost::thread* t = new boost::thread{ CCG_grid_PA_experiment_STPsolution_very_large_fastMST };
	threads.add_thread(t);

	threads.join_all();

}
#pragma endregion parallel_experiments



int main()
{
	srand(time(NULL)); //  seed random number generator


	non_parallel_experiments();

	cout << "END" << endl;
	getchar();
}