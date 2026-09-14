#!/bin/bash -xe
echo $PATH
which z3
which cvc5
which mathsat
which bitwuzla
z3 -version
cvc5 --version | head -n 3
mathsat -version
bitwuzla --version
mvn --version
echo "All solvers available!"