#!/usr/bin/env python2.7
# -*- coding: UTF-8 -*-

import xml.etree.ElementTree as ET
import os
import subprocess
import sys
import argparse

argparser = argparse.ArgumentParser(description="Parse SVCOMP Result XML Files.")
argparser.add_argument('directory', type=str, nargs='?', help='The directory ' +
        'containing .xml result files. The default is the current directory.',
        default=os.getcwd())
argparser.add_argument('-p', '--printunsound', action='store_true', help='Print ' +
        'unsound files to corresponding result .xml file')
argparser.add_argument('-v', '--verbose', action='store_true', help='Turn on verbose output.')

args = argparser.parse_args()

if len(sys.argv) == 2:
    dirname = sys.argv[1]

unsounds = set()
i=0
def parsexml(filename):
    global i
    "Parses a result file from SVCOMP"
    tree = ET.parse(filename)
    root = tree.getroot()
    urlBase = "https://sv-comp.sosy-lab.org/2017/results/results-verified/"
    suffix = ".".join(os.path.basename(filename).split(".")[:2])
    url = urlBase + suffix + '.logfiles/sv-comp17.'
    origTmpFilename = "tmp"

    currentunsound = set()

    for run in root.findall('run'):
        testFilename = run.get('files').split("/")[4].split("]")[0];
        for column in run.iter('column'):
            key = column.get('title')
            value = column.get('value')

            if key == "category" and value == "wrong":
                i=i+1
                tmpFilename = origTmpFilename + str(i) + '-' + testFilename
                dlUrl = url + testFilename + ".log"
                print "Downloading "+dlUrl
                sha = subprocess.Popen(['wget', '-t','3','-qO',tmpFilename,dlUrl], stdout=subprocess.PIPE).communicate()[0]
                unsounds.add(run.get('name'))
                if args.printunsound:
                    currentunsound.add(run.get('name'))

    if args.printunsound and len(currentunsound) > 0:
        print filename

        for element in currentunsound:
            print element

        print ""


for filename in os.listdir(args.directory):
    if filename.endswith(".xml"):
        if args.verbose:
            print "Parsing " + filename + " ..."

        parsexml(args.directory + "/" + filename)

print ""
print "Unsound accumulated files: "
for element in unsounds:
    print element
