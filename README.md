# incremental-examples
Some examples of using incremental SAT solvers (SAT/SMT/AR Summer School 2024)

# 0. Setup CaDiCaL

cd cadical
./configure
make

# 1. HCP2DIMACS example

cd 1_dimacs
make
./hcp2dimacs ../graphs/small-example.hcp | ../cadical/build/cadical

- The following example takes ~21 seconds (49950 variables, 11039524 clauses):
./hcp2dimacs ../graphs/fhcpcs-graph28.hcp | ../cadical/build/cadical

# 2. HCP2IPASIR example

cd 2_ipasir
make
time ./hcp2ipasir ../graphs/small-example.hcp
time ./hcp2ipasir ../graphs/fhcpcs-graph1.hcp

- The following example now takes only ~4 seconds:
time ./hcp2ipasir ../graphs/fhcpcs-graph28.hcp

- The larger example needs more than 2 minutes:
time ./hcp2ipasir ../graphs/fhcpcs-graph70.hcp

# 3. HCP2CEGAR example

cd 3_ipasir_cegar
make
time ./hcp2cegar ../graphs/small-example.hcp
time ./hcp2cegar ../graphs/fhcpcs-graph1.hcp

- Takes ~0,052s and 208 iterations:
time ./hcp2cegar ../graphs/fhcpcs-graph28.hcp

- Takes ~0,179s and 323 iterations:
time ./hcp2cegar ../graphs/fhcpcs-graph70.hcp

# 4. HCP2IPASIRUP example

cd 4_ipasirup
make

time ./hcp2ipasirup ../graphs/small-example.hcp
time ./hcp2ipasirup ../graphs/fhcpcs-graph1.hcp

- Takes ~0,015s and 41 sub-cycle is detected:
time ./hcp2ipasirup ../graphs/fhcpcs-graph28.hcp

- Takes ~0,075s and 183 sub-cycle is detected:
time ./hcp2ipasirup ../graphs/fhcpcs-graph70.hcp