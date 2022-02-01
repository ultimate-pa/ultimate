#!/bin/bash
pushd ltl-realworld
for f in *.c; do gcc -E -P -m64 $f > $(basename $f).i; done
make -j2 CC=gcc
make clean
make -j2 CC=clang
make clean
popd

pushd ltl-eca
for f in *.c; do gcc -E -P -m64 $f > $(basename $f).i; done
make -j2 CC=gcc
make clean
make -j2 CC=clang
make clean
popd
pushd ltl-toy
for f in *.c; do gcc -E -P -m64 $f > $(basename $f).i; done
make -j2 CC=gcc
make clean
make -j2 CC=clang
make clean
popd
