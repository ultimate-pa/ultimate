#!/bin/bash
zip -r RecursivePrograms.zip  RecursivePrograms
chmod 755 RecursivePrograms.zip
scp ./RecursivePrograms.zip heizmann@sotec.informatik.uni-freiburg.de:/export/server/httpd/ultimate/automizer/
