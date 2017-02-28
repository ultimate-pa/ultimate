import argparse
import datetime
import logging
import os.path
import sys

import logging_system


class cliparser(object):
    "Command Line Argument Parser"

    def __init__(self):
        "Initializes the command line arguments"
        __argparser__ = argparse.ArgumentParser(description="Identify differences in results " + 
                                            "of two SV-COMP verifiers. Searches all files in a " + 
                                            "given directory for differences.")
        
        __argparser__.add_argument('tool', metavar='TOOL', type=str,
                               help='The name of the verifier to compare the results for.')
        
        __argparser__.add_argument('base', metavar='BASE', type=str,
                               help='The name of the verifier to compare the results with.')
        
        __argparser__.add_argument('directory',
                               metavar='DIRECTORY',
                               type=str,
                               help='The directory containing SV-COMP .xml result files.')
        
        __argparser__.add_argument('-t', '--testoutput', action='store_true',
                                   help='Produce Ultimate test suite compatible output for copy-pasting.')
        
        __argparser__.add_argument('-v', '--verbose', type=str, choices=['DEBUG', 'DEBUGIO'],
                                   help='Enable verbose output with specified log level. ' + 
                                   'DEBUG prints debug messages, ' + 
                                   'DEBUGIO prints debug messages and debug I/O messages')
        
        __argparser__.add_argument('-y', '--year', type=int, nargs=1,
                                   help='The year of the SV-COMP results. This is used for parsing the ' + 
                                   'output logs. E.g., 2017. Defaults to current year.')
        
        __argparser__.add_argument('-l', '--print-output-links', action='store_true',
                                   help='Print the links to the respective console output.')
        
        __argparser__.add_argument('-n', '--no-filename-sanitizing', action='store_true',
                                   help='Do not remove relative paths in SVCOMP benchmark file names. ' + 
                                   'This option overwrites the --benchmark-prefix option.')
        
        __argparser__.add_argument('-p', '--benchmark-prefix', type=str,
                                   default="examples/svcomp/",
                                   help='Specifies the (relative) location of the SVCOMP benchmarks. ' + 
                                   'Default: "examples/svcomp/"')
        
        __argparser__.add_argument('-s', '--testoutput-with-settings', action='store_true',
                                   help='Produce Ultimate test suite compatible output with corresponding settings. ' + 
                                   'This setting overwrites the --testoutput setting.')
        
        __argparser__.add_argument('-c', '--comparison-output', action='store_true',
                                   help='Specifies that a test suite run for the comparison tool should also be generated. ' + 
                                   'This option only works in combination with the --testoutput-with-settings flag.')
        
        __argparser__.add_argument('-f', '--file', type=str,
                                   help='Specifies one single file to be analyzed instead of the whole directory. ' + 
                                   'The directory must still be provided in order to be able to compare the run.')
        
        __argparser__.add_argument('-i', '--ignore-correct', action='store_true',
                                   help="Ignores the benchmark, if the tool gave the correct answer, but the comparison " + 
                                   "tool did not.")
        
        __argparser__.add_argument('-u', '--display-unsounds', action='store_true',
                                   help="Also display an extra list with all unsound results.")
        
        __argparser__.add_argument('-o', '--output', type=str,
                                   help='Specifies the name of the file the output should be written to.')
        
        self.__args__ = __argparser__.parse_args()

    def getTool(self):
        "Returns the tool."
        return self.__args__.tool
    
    def getBase(self):
        "Returns the base tool."
        return self.__args__.base
    
    def getDirectory(self):
        "Returns the working directory."
        if self.__args__.directory.endswith("/"):
            return self.__args__.directory
        else:
            return self.__args__.directory + "/"
    
    def getYear(self):
        "Returns the year if any is set."
        if not self.__args__.year:
            return datetime.datetime.now().year
        
        return self.__args__.year
    
    def getFile(self):
        "Returns the file to be analyzed"
        
        if not self.__args__.file:
            return ""

        sanitizedFile = os.path.basename(self.__args__.file)

        if not os.path.isfile(self.getDirectory() + sanitizedFile):
            sys.stderr.write("File not found: " + str(self.__args__.file))
            sys.exit(1)
        
        return str(sanitizedFile)
    
    def printTestOutput(self):
        "Returns true if test output is enabled."
        return self.__args__.testoutput
    
    def printTestOutputWithSettings(self):
        "Returns true if test output with corresponding settings is enabled."
        return self.__args__.testoutput_with_settings
    
    def printOutputLinks(self):
        "Returns true if output links should be printed"
        return self.__args__.print_output_links
    
    def nofilenamesanitizing(self):
        "Returns true if SVCOMP benchmark filenames should not be sanitized"
        return self.__args__.no_filename_sanitizing
    
    def printComparisonOutput(self):
        "Returns true if the test suite run for the comparison tool should also be printed"
        return self.__args__.comparison_output
    
    def ignoreCorrect(self):
        "Returns true if correct results should be ignored (if the comparison tool was incorrect)"
        return self.__args__.ignore_correct
    
    def displayUnsounds(self):
        "Returns true if unsound results should be displayed"
        return self.__args__.display_unsounds
    
    def getOutputFileName(self):
        "Returns the file name of the output file"
        
        if not self.__args__.output:
            return ""
        
        return str(self.__args__.output)
    
    def getbenchmarksprefix(self):
        "Returns the prefix for the SVCOMP benchmarks"
        
        # Ignore this setting if --no-filename-sanitizing is enabled.
        if self.__args__.no_filename_sanitizing:
            return ""
        
        if not self.__args__.benchmark_prefix:
            return "examples/svcomp/"
        
        if not self.__args__.benchmark_prefix.endswith("/"):
            return self.__args__.benchmark_prefix + "/"
        else:
            return self.__args__.benchmark_prefix
    
    def getVerbose(self):
        "Returns the verbosity level."
        if not self.__args__.verbose:
            return logging.INFO
        
        if self.__args__.verbose == "DEBUG":
            return logging.DEBUG
        
        if self.__args__.verbose == "DEBUGIO":
            return logging_system.__DEBUG_LEVEL_IO__
        
        raise Exception("Debug level " + self.__args__.verbose + " not defined.")
