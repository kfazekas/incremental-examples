# incremental-examples
Some examples of using incremental SAT solvers (SAT/SMT/AR Summer School 2024).
Check it out with:
```bash
git clone git@github.com:kfazekas/incremental-examples.git
```

# 0. Setup CaDiCaL

```bash
cd cadical
./configure
make
```

# 1. HCP2DIMACS example

```bash
cd 1_dimacs
make
./hcp2dimacs ../graphs/small-example.hcp | ../cadical/build/cadical
```
- The following example takes ~21 seconds (49950 variables, 11039524 clauses):
```bash
./hcp2dimacs ../graphs/fhcpcs-graph28.hcp | ../cadical/build/cadical
```
# 2. HCP2IPASIR example

```bash
cd 2_ipasir
make
time ./hcp2ipasir ../graphs/small-example.hcp
time ./hcp2ipasir ../graphs/fhcpcs-graph1.hcp
```
- The following example now takes only ~4 seconds:

```bash
time ./hcp2ipasir ../graphs/fhcpcs-graph28.hcp
```
- The larger example needs more than 2 minutes:

```bash
time ./hcp2ipasir ../graphs/fhcpcs-graph70.hcp
```

# 3. HCP2CEGAR example
```bash
cd 3_ipasir_cegar
make
time ./hcp2cegar ../graphs/small-example.hcp
time ./hcp2cegar ../graphs/fhcpcs-graph1.hcp
```

- Takes ~0,052s and 208 iterations:
```bash
time ./hcp2cegar ../graphs/fhcpcs-graph28.hcp
```

- Takes ~0,179s and 323 iterations:
```bash
time ./hcp2cegar ../graphs/fhcpcs-graph70.hcp
```

# 4. HCP2IPASIRUP example

```bash
cd 4_ipasirup
make
time ./hcp2ipasirup ../graphs/small-example.hcp
time ./hcp2ipasirup ../graphs/fhcpcs-graph1.hcp
```

- Takes ~0,015s and 41 sub-cycle is detected:
```bash
time ./hcp2ipasirup ../graphs/fhcpcs-graph28.hcp
```

- Takes ~0,075s and 183 sub-cycle is detected:
```bash
time ./hcp2ipasirup ../graphs/fhcpcs-graph70.hcp
```