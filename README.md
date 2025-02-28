These are the C++ codes and datasets for the Node-Weighted Partial Terminal Steiner Tree Problem (NWPTSTP) in our paper:

Yahui Sun, Daniel Rehfeldt, Marcus Brazil, Doreen Thomas, and Saman Halgamuge. “A Physarum-inspired algorithm for minimum-cost relay node placement in wireless sensor networks” IEEE/ACM Transactions on Networking (2020)

For any enquiry, please feel free to contact Yahui SUN: yahuisun@outlook.com


# C++ Codes

The codes are in the <b>PA_WSN.cpp</b> file. 

<b>It is recommended to fold all the regions of codes for easy reading</b> (by pressing Ctrl+M+O in VisualStudio)：
1) the codes for our PSTA algorithm are in the "PSTA" region, i.e., the codes below "/\*PSTA\*/".
2) the codes for the GKA algorithm are in the "Guha_16103" region.
3) the codes for the RRPL and OSRP algorithms are in the "two relay node placement algorithms" region.
4) the codes for the experiments in our paper are in the "experiments" region.

Running these codes requires some header files in the Boost library: https://www.boost.org/ and my own YS-Graph-Library: https://github.com/YahuiSun/YS-Graph-Library (see ysgraph_20200219.zip) 

Notably, #include "pch.h" is generated by Visual Studio: https://stackoverflow.com/questions/54121917/what-is-pch-h-and-why-is-it-needed-to-be-included-as-the-first-header-file 

After making the header files ready, all the experiment results in our paper can be produced by runnning the codes in the "non_parallel_experiments" region, i.e., you can run:

int main()
{

	srand(time(NULL)); //  seed random number generator
	
	non_parallel_experiments();
	
	cout << "END" << endl;
	
	getchar();
}

To read these C++ codes in detail, I suggest to start from the "non_parallel_experiments" region. You may then trace the more detailed codes in regions like "PSTA" etc. It takes some time to look through all these codes. For any enquiry, please feel free to contact Yahui SUN: yahuisun@outlook.com 

# Datasets

These are 6000 instances for NWPTSTP in total. 

The optimal solution costs of these instances are in the "opt6000_single_column.csv" file.

These instances are randomly generated for the minimum-cost relay node placement experiments in our paper, and can be transformed to instances for the Node-Weighted Steiner Tree Problem (NWSTP) using a theorem in our paper. 



The content in each instance are as follows.

SECTION Graph 

Nodes XXX : the total number of vertices

Edges XXX : the total number of edges

E v1 v2 XX : an edge (v1,v2) with cost XX


SECTION Terminals

T v1 : a compulsory vertex v1

TL v2 : a compulsory leaf vertex v2


SECTION NodeWeights

NW XXX: the node weights (from 1 to |V|; only non-compulsory vertices have positive node weights)


