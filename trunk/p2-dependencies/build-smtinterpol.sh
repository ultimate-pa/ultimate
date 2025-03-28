#!/bin/bash
git clone https://github.com/schuessf/smtinterpol.git smtinterpol
cd smtinterpol
# TODO: This does not yield the "correct" MANIFEST.MF
# What can we do about this?
ant stage
mv dist/* ..
cd ..
rm -rf smtinterpol
