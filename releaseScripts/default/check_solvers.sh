#!/bin/bash -xe
echo $PATH
which z3
which cvc4
which mathsat
z3 -version
cvc4 --version | head -n 3
mathsat -version
mvn --version
echo "All solvers available!"