#!/bin/sh
rm -Rf UltimateEliminator+MathSAT/UltimateCommandline.zip UltimateEliminator+MathSAT/StarExecArchive/
rm -Rf UltimateEliminator+SMTInterpol/UltimateCommandline.zip UltimateEliminator+SMTInterpol/StarExecArchive/
rm -Rf UltimateEliminator+Yices2/UltimateCommandline.zip UltimateEliminator+Yices2/StarExecArchive/
pushd UltimateEliminator+MathSAT
./createZip.sh
cp UltimateCommandline.zip ../UltimateEliminator+MathSAT.zip
popd
pushd UltimateEliminator+SMTInterpol
./createZip.sh
cp UltimateCommandline.zip ../UltimateEliminator+SMTInterpol.zip
popd
pushd UltimateEliminator+Yices2
./createZip.sh
cp UltimateCommandline.zip ../UltimateEliminator+Yices2.zip
popd
