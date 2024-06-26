#include <iostream>
#include <fstream>
#include <sstream>
#include <cassert>
#include <vector>
#include <iomanip>

// Number of nodes and edges
int nNode, nEdge;

// Adjacency Matrix
// adjMtx[i][j] > 0 <-> there is an edge from node (i+1) to node (j+1)
std::vector<std::vector<int>> adjMtx;

// The last Boolean variable that corresponds to the edges of the input graph
int lastEdgeID;

// Position matrix:
// posMtx[i][j] true <-> node (i+1) is visited at position j in the solution
std::vector<std::vector<int>> posMtx;

// Degree of each node (i+1)
std::vector <int> nodeDegree;

// Node minNode has minimum degree (not shifted, node ID, not vector position)
int minNode;

// Fills in the adjancency matrix and finds a node with the minimal degree.
bool parse_hcp_file (const std::string file_name) {
  std::ifstream input_file_stream(file_name);
  std::string line;

  nNode = 0;
  nEdge = 0;
  lastEdgeID = 0;

  if (!input_file_stream.is_open()) {
    std::cerr << "Could not open file '" << file_name << "'. " << std::endl;  
    return true;
  }
  
  const std::string delim(":");
  const std::string size_tag("DIMENSION");

  while (std::getline(input_file_stream, line)) {
    std::istringstream line_stream(line);
    std::string term;
    std::vector<std::string> tokens;
    std::vector<int> int_terms;
    bool meta_line = false;
    bool size_line = false;

    while (line_stream >> term) {
      tokens.push_back(term);
      if (term == delim) meta_line = true;
      if (term == size_tag) size_line = true;

      bool has_only_digits = (term.find_first_not_of( "0123456789" ) == std::string::npos);
      if (has_only_digits) {
        int_terms.push_back(std::stoi(term));
      }
    }
    
    if (size_line) {
      if (int_terms.size() != 1 || nNode) {
        std::cerr << "Could not parse dimension of graph." << std::endl;
        return true;
      }
      
      nNode = int_terms[0];
      
      adjMtx = std::vector< std::vector<int> > (nNode, std::vector<int>(nNode,0));
      nodeDegree = std::vector<int> (nNode,0);
    
    } else if (!meta_line && int_terms.size() == 2) {
      assert (adjMtx.size());
      assert (!adjMtx[int_terms[0]-1][int_terms[1]-1]);

      adjMtx[int_terms[0]-1][int_terms[1]-1] = ++lastEdgeID;
      adjMtx[int_terms[1]-1][int_terms[0]-1] = ++lastEdgeID;
      nodeDegree[int_terms[0]-1]++;
      nodeDegree[int_terms[1]-1]++;

      nEdge++;
    }
  }

  input_file_stream.close();

  // Find a node with minimal degree
  minNode = 1;
  int min_degree = nodeDegree[minNode-1];

  for (int i = 0; i < nNode; i++) {
    if (nodeDegree[i] < min_degree) { 
      min_degree = nodeDegree[i];
      minNode = i+1;
    }
  }
  
  return false;
};

// Encodes that exactly one of the variables of 'vars' is allowed to be true
// v1 + v2 + ... + vn = 1
void exactly_one_constraint(std::vector<int> vars) {
  std::cout << "c EO [ " ;
  for (auto const v: vars) std::cout << v << " ";
  std::cout << "]" << std::endl;

  /* 
    At most one of the variables is true: 
    v1 => ~v2 /\ v1 => ~v3 ̣/\ ... /\ v1 => ~vn /\
    v2 => ~v1 /\ v2 => ~v3 /\ ... /\ v2 => ~vn /\
    ...
  */
  for (unsigned i = 0; i < vars.size(); i++) {
    for (unsigned j = i+1; j < vars.size(); j++) {
      std::cout << -vars[i] << " " << -vars[j] << " 0" << std::endl;
    }
  }

  // At least one of the variables is true: v1 \/ v2 \/ ... \/ vn
  for (auto const v: vars) {
    std::cout << v << " ";
  }
  std::cout << "0" << std::endl;
};


// Generate nNode*nNode Boolean variables where
// posMtx[i][j] true <-> node (i+1) is at position j in the solution
void init_position_matrix (int last_edge_var, int first_node) {
  int pos_var = last_edge_var;

  posMtx = std::vector< std::vector<int> > (nNode, std::vector<int>(nNode,0));
  std::vector<int> possible_positions;
  
  // Node (i+1) can be on exactly one of the positions between [0..nNode]
  for (int i = 0; i < nNode; i++) {
    possible_positions.clear();
    for (int j = 0; j < nNode; j++) {
      posMtx[i][j] = ++pos_var;
      possible_positions.push_back(pos_var);
    }
    exactly_one_constraint (possible_positions);
  }

  // There can be exactly one node at each position
  for (int i = 0; i < nNode; i++) {
    possible_positions.clear();
    for (int j = 0; j < nNode; j++) {
      possible_positions.push_back(posMtx[j][i]);
    }
    exactly_one_constraint (possible_positions);
  }
  
  // At the first position there is a node with minimal degree:
  std::cout << posMtx[first_node-1][0] << " 0" << std::endl;
};


// Pretty prints the Boolean variables representing edges of the graph
void print_adjMtx () {
  for (int i = 0; i < nNode; i++) {
    std::cout << "c ";
    for (int j = 0; j < nNode; j++) {
      std::cout << std::setw(3);
      std::cout << adjMtx[i][j] << "  ";
    }
    std::cout << std::endl;
  }

  for (int i = 0; i < nNode; i++) {
    for (int j = 0; j < nNode; j++) {
      if (adjMtx[i][j]) {
        std::cout << "c Edge " << i+1 << "->" << j+1 << " <-> variable " << adjMtx[i][j] << std::endl;
      }
    }
  }
};


// Construct degree constraint: For each node exactly one outgoing and exactly
// one incomming edge must be selected.
int add_degree_constraints (bool only_count = false) {
  int clause_count = 0; 
  
  //1. Exactly one outgoing edge is selected:
  for (int i = 0; i < nNode; i++) {
    std::vector<int> neighbours;
    for (int j = 0; j < nNode; j++) {
      if (adjMtx[i][j]) neighbours.push_back(adjMtx[i][j]);
    }
    clause_count += neighbours.size() * (neighbours.size() -1) / 2 + 1;
    if (!only_count) exactly_one_constraint (neighbours);
  }

  //2. Exactly one incomming edge is selected:
  for (int i = 0; i < nNode; i++) {
    std::vector<int> neighbours;
    for (int j = 0; j < nNode; j++) {
      if (adjMtx[j][i]) neighbours.push_back(adjMtx[j][i]);
    }
    clause_count += neighbours.size() * (neighbours.size() -1) / 2 + 1;
    if (!only_count) exactly_one_constraint (neighbours);
  }

  // No 2-long subcycles:
  for (int i = 0; i < nNode; i++) {
    for (int j = i+1; j < nNode; j++) {
      if (adjMtx[i][j]) {
        clause_count++;
        if (!only_count) std::cout << -adjMtx[i][j] << " " << -adjMtx[j][i] << " 0" << std::endl;
      }
    }
  }

  return clause_count;
};

// Probihit formation of sub-cycles 
int add_connectivity_constraint (bool only_count = false) {
  int clause_count = 0;

  // The cycle must start and end at minNode:
  for (int i = 0; i < nNode; i++) {
    if (adjMtx[minNode-1][i]) {
      // The selected successor of the minNode is the second node in the position mtx
      if (only_count) clause_count++;
      else std::cout << -adjMtx[minNode-1][i] << " " << posMtx[i][1] << " 0" << std::endl;
    }
    if (adjMtx[i][minNode-1]) {
      // The selected predecessor of minNode is the last node in the position mtx.
      if (only_count) clause_count++;
      else std::cout << -adjMtx[i][minNode-1] << " " << posMtx[i][nNode-1] << " 0" << std::endl;
    }
  }

  for (int i = 1; i < nNode; i++) {
    for (int j = 1; j < nNode; j++) {
      if (i == j || !adjMtx[i][j]) continue;
      for (int p = 1; p < nNode-1; p++) {
        if (only_count) clause_count++;
        else std::cout << -adjMtx[i][j] << " " << -posMtx[i][p] << " " << posMtx[j][p+1] << " 0" << std::endl;
      }
    }
  } 

  return clause_count;
};

int main(int argc, char* argv[])
{
  if (argc < 2) {
    std::cout << "Usage: ./hcp2dimacs graph-file" << std::endl;
    return 1;
  }

  if (parse_hcp_file (argv[1])) return 1;

  // Print some basic statistics
  std::cout << "c Number of nodes: " << nNode << std::endl;
  std::cout << "c Number of edges: " << nEdge << std::endl;
  std::cout << "c Node with smallest degree: " << minNode + 1 << std::endl;

  print_adjMtx ();

  int nVar = 2*nEdge + nNode*nNode;
  int nClauses = add_degree_constraints(true);
  nClauses += add_connectivity_constraint (true);
  nClauses += 2 * nNode * ((nNode * (nNode-1))/2 + 1) + 1; // position matrix

  // Print DIMACS header
  std::cout << "p cnf " << nVar << " " << nClauses << std::endl;

  // Unary encoding of position of each node:
  init_position_matrix (lastEdgeID, minNode);
  add_degree_constraints(); 
  add_connectivity_constraint();

};
