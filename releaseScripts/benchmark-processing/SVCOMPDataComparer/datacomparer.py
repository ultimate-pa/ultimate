#! /usr/bin/env python2

from fnmatch import fnmatch
from logging import debug
import os

from helpers.cli import cliparser
from helpers.logging_system import initialize_logger, debugio
from helpers.output import Output
from svcomp_xml.parser import SVCOMPParser


cli = cliparser()
tool = cli.getTool()
comparetool = cli.getBase()
directory = cli.getDirectory()
fileToAnalyze = cli.getFile()
testoutput = cli.printTestOutput()
testoutputsettings = cli.printTestOutputWithSettings()
year = cli.getYear()
printOutputLinks = cli.printOutputLinks()
noFileSanitizing = cli.nofilenamesanitizing()
benchmarksPrefix = cli.getbenchmarksprefix()
comparisonOutput = cli.printComparisonOutput()
ignoreCorrect = cli.ignoreCorrect()
displayUnsounds = cli.displayUnsounds()
outputFilename = cli.getOutputFileName()
initialize_logger(cli.getVerbose())
debug("Initializing...")
debug("Tool: " + tool)
debug("Base: " + comparetool)
debug("Dir : " + directory)
debug("File to be analyzed: " + ("All in directory" if fileToAnalyze == "" else fileToAnalyze))
debug("Test output: " + str(testoutput))
debug("Test output with settings: " + str(testoutputsettings))
debug("Comparison output in tests: " + str(comparisonOutput))
debug("Ignore correct: " + str(ignoreCorrect))
debug("Display unsound results: " + str(displayUnsounds))
debug("Year: " + str(year))
debug("Print output links: " + str(printOutputLinks))
debug("Turn off filename sanitizing: " + str(noFileSanitizing))
debug("Benchmarks prefix: " + str(benchmarksPrefix))
debug("Output filename: " + str(outputFilename))


def determinetoolbenchmark(filename):
    splits = filename.split("/")
    name = splits[-1]
    
    nameParts = name.split(".")
    
    toolname = nameParts[0]
    date = nameParts[1]
    benchmark = ".".join(nameParts[2:])
    category = nameParts[4]
    
    return toolname, date, benchmark, category

def parsing(basefile, comparefile):
    
    debug("Parsing base file:       " + basefile)
    resultBase = parser.parsexml(basefile)
    
    debug("Parsing comparison file: " + comparefile)
    resultCompare = parser.parsexml(comparefile)
    
    results = {}
    unsounds = {}

    for to in resultCompare.__runs__:
        baseRun = resultBase.getnametorun(to['name'])
        
        same, other = baseRun.hassameresult(to, ignoreCorrect)
        
        key = str(baseRun['status'])

        if noFileSanitizing:
            name = str(baseRun['name'])
        else:
            name = str(baseRun.getsanitizedname())
        
        if not same:
            if key in results:
                if other in results[key]:
                    olddict = results[key]
                    oldlist = olddict[other]
                    oldlist.append((name, baseRun.getlogurl(), to.getlogurl()))
                    olddict[other] = oldlist
                    results[key] = olddict
                else:
                    storedict = {}
                    storedict[other] = [(name, baseRun.getlogurl(), to.getlogurl())]
                    results[key] = storedict
            else:
                ot = {}
                ot[other] = [(name, baseRun.getlogurl(), to.getlogurl())]
                results[key] = ot
        
        if baseRun['category'] == "wrong":
            if key in unsounds:
                oldlist = unsounds[key]
                oldlist.append((name, baseRun.getlogurl()))
                unsounds[key] = oldlist
            else:
                unsounds[key] = [(name, baseRun.getlogurl())]
            
    return results, unsounds


parser = SVCOMPParser(year)

if fileToAnalyze == "":
    files = os.listdir(directory)
else:
    files = [fileToAnalyze]
    
compareFiles = os.listdir(directory)
debug("Read directory " + directory)
debugio("Detected files:\n   " + "\n   ".join(files))

fileresults = {}
fileunsounds = {}

for filename in files:
    if filename.startswith(tool) and filename.endswith(".xml"):
        tool, date, benchmark, category = determinetoolbenchmark(filename)
        
        for comparefile in compareFiles:
            if fnmatch(comparefile, comparetool + "*" + benchmark):
                results, unsounds = parsing(directory + filename, directory + comparefile)
                if len(results) > 0:
                    fileresults[filename] = results
                if len(unsounds) > 0:
                    fileunsounds[filename] = unsounds
                break

output = Output(outputFilename)

# Test output with settings overwrites all other output modes
if testoutputsettings:
    output.printUltimateResultWithSettings(fileresults, fileunsounds, tool, comparetool, printOutputLinks, comparisonOutput, benchmarksPrefix, year, displayUnsounds)
else:
    if testoutput:
        output.printUltimateResult(fileresults, fileunsounds, tool, comparetool, printOutputLinks, benchmarksPrefix, displayUnsounds)
    else:
        output.printResult(fileresults, fileunsounds, tool, comparetool, printOutputLinks, benchmarksPrefix, displayUnsounds)

print ""
print "DONE."