#!/usr/bin/env python2.7
# -*- coding: UTF-8 -*-

import xml.etree.ElementTree as ET
import subprocess
import os
import sys
import argparse
import urllib

argparser = argparse.ArgumentParser(description="Parse SVCOMP Result XML Files.")
argparser.add_argument('directory', type=str, nargs='?', help='The directory ' +
        'containing .xml result files. The default is the current directory.',
        default=os.getcwd())
argparser.add_argument('-p', '--printerror', action='store_true', help='Print ' +
        'error files to corresponding result .xml file')
argparser.add_argument('-v', '--verbose', action='store_true', help='Turn on verbose output.')

args = argparser.parse_args()

if len(sys.argv) == 2:
    dirname = sys.argv[1]


errors = set()
errorMessages = {}
i=0
def parsexml(dir, filename):
    global i
    fullXmlFilename = dir + "/" + filename
    
    urlBase = "https://sv-comp.sosy-lab.org/2017/results/results-verified/"
    suffix = ".".join(os.path.basename(filename).split(".")[:2])
    url = urlBase + suffix + '.logfiles/sv-comp17.'
    origTmpFilename = "tmp"
    "Parses a result file from SVCOMP"
    tree = ET.parse(fullXmlFilename)
    root = tree.getroot()

    currenterror = set()

    for run in root.findall('run'):
        #print(run.get('files').split("/"))
        testFilename = run.get('files').split("/")[4].split("]")[0];
        #print testFilename
        for column in run.iter('column'):
            key = column.get('title')
            value = column.get('value')

            if key == "status" and value == "ERROR":
                i=i+1  
                tmpFilename = origTmpFilename + str(i)
                print testFilename
                errors.add(run.get('name'))
                if args.printerror:
                    currenterror.add(run.get('name'))
                
                # receive log file from server
                dlUrl = url + testFilename + ".log"
                print "Downloading "+dlUrl
                sha = subprocess.Popen(['wget', '-t','3','-qO',tmpFilename,dlUrl], stdout=subprocess.PIPE).communicate()[0]
                #urllib.urlretrieve(url + testFilename + ".log", filename=tmpFilename)
                
                # search for error keyword and increment occurrence counter
                for line in open(tmpFilename):
                    if "ERROR:" in line:
                        if line in errorMessages:
                            errorMessages[line]+=1
                        else:
                            errorMessages[line] = 1
                        #print line
                        break

    if args.printerror and len(currenterror) > 0:
        print fullXmlFilename

        for element in currenterror:
            print element

        print ""


for filename in os.listdir(args.directory):
    if filename.endswith(".xml"):
        if args.verbose:
            print "Parsing " + filename + " ..."

        parsexml(args.directory, filename)

print ""
print "Error files accumulated: "
for element in errors:
    print element

print "Error files accumulated with occurrence counters: "
for key, value in errorMessages.iteritems():
    print str(value) + "x " + key
