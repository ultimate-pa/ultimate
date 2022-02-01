#!/usr/bin/env python2.7

from __future__ import print_function
import sys
import subprocess
import os
import fnmatch
import platform
import argparse


version = 'f286451a'
writeUltimateOutputToFile = True
outputFileName = 'Ultimate.log'
errorPathFileName = 'UltimateCounterExample.errorpath'

# various settings file strings 
settingsFileMemSafetyDerefMemtrack = 'DerefFreeMemtrack'
settingsFileMemSafetyDeref = 'Deref'
settingsFileOverflow = 'Overflow'
settingsFileTermination = 'Termination'
settingsFileReach = 'Reach'
settingsFileBitprecise = 'Bitvector'
settingsFileDefault = 'Default'
settingsFile32 = '32bit'
settingsFile64 = '64bit'

# special strings in ultimate output
unsupportedSyntaxErrorString = 'ShortDescription: Unsupported Syntax'
incorrectSyntaxErrorString = 'ShortDescription: Incorrect Syntax'
typeErrorString = 'Type Error'
exceptionErrorString = 'ExceptionOrErrorResult'
safetyString = 'Ultimate proved your program to be correct'
allSpecString = 'AllSpecificationsHoldResult'
unsafetyString = 'Ultimate proved your program to be incorrect'
memDerefFalseString = 'pointer dereference may fail'
memDerefFalseString2 = 'array index can be out of bounds'
memFreeFalseString = 'free of unallocated memory possible'
memMemtrackFalseString = 'not all allocated memory was freed'
terminationFalseString = 'Found a nonterminating execution for the following lasso shaped sequence of statements'
terminationTrueString = 'TerminationAnalysisResult: Termination proven'
errorPathBeginString = 'We found a FailurePath:'
terminationPathEnd = 'End of lasso representation.'
overflowFalseString = 'overflow possible'


def setBinary():
    currentPlatform = platform.system()
    
    if currentPlatform == 'Windows':
        ultimateBin = 'eclipsec.exe'
    else:
        ultimateBin = "Ultimate"
    
    # check if ultimate bin is there 
    if not os.path.isfile(ultimateBin):
        print("Ultimate binary not found, expected " + ultimateBin)
        sys.exit(1)
    
    if not currentPlatform == 'Windows':
        ultimateBin = './' + ultimateBin
    
    ultimateBin = ultimateBin + ' --console'
    return ultimateBin


def searchCurrentDir(searchstring):
    for root, dirs, files in os.walk(os.getcwd()):
        for name in files:
            if fnmatch.fnmatch(name, searchstring):
                return os.path.join(root, name)
        break    
    return 


def containsOverapproximationResult(line):
    triggers = ['Reason: overapproximation of bitwiseAnd', 'Reason: overapproximation of bitwiseOr', 'Reason: overapproximation of bitwiseXor', 'Reason: overapproximation of shiftLeft', 'Reason: overapproximation of shiftRight', 'Reason: overapproximation of bitwiseComplement']
    
    for trigger in triggers:
        if line.find(trigger) != -1:
            return True
    
    return False


def runUltimate(ultimateCall, terminationMode):
    print('Calling Ultimate with: ' + ultimateCall)
    
    try:
        ultimateProcess = subprocess.Popen(ultimateCall, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
    except:
        print('Error trying to open subprocess')
        sys.exit(1)
    
    
    safetyResult = 'UNKNOWN'
    memResult = 'NONE'
    readingErrorPath = False
    overapprox = False
    
    # poll the output
    ultimateOutput = ''
    errorPath = ''
    while True:
        line = ultimateProcess.stdout.readline().decode('utf-8', 'ignore')
        if readingErrorPath:
            errorPath += line
        ultimateOutput += line
        sys.stdout.write('.')
        # sys.stdout.write('Ultimate: ' + line)
        sys.stdout.flush()
        if (line.find(unsupportedSyntaxErrorString) != -1):
            safetyResult = 'ERROR: UNSUPPORTED SYNTAX'
        elif (line.find(incorrectSyntaxErrorString) != -1):
            safetyResult = 'ERROR: INCORRECT SYNTAX'
        elif (line.find(typeErrorString) != -1):
            safetyResult = 'ERROR: TYPE ERROR'
        elif (line.find(exceptionErrorString) != -1):
            safetyResult = 'ERROR: ' + line            
        if(not overapprox and containsOverapproximationResult(line)):
            overapprox = True
        if (terminationMode):
            if (line.find(terminationTrueString) != -1):
                safetyResult = 'TRUE'
            if (line.find(terminationFalseString) != -1):
                safetyResult = 'FALSE(TERM)'
                readingErrorPath = True
            if (line.find(terminationPathEnd) != -1):
                readingErrorPath = False
        else:
            if (line.find(safetyString) != -1 or line.find(allSpecString) != -1):
                safetyResult = 'TRUE'
            if (line.find(unsafetyString) != -1):
                safetyResult = 'FALSE'
            if (line.find(memDerefFalseString) != -1):
                memResult = 'valid-deref'
            if (line.find(memDerefFalseString2) != -1):
                memResult = 'valid-deref'
            if (line.find(memFreeFalseString) != -1):
                memResult = 'valid-free'
            if (line.find(memMemtrackFalseString) != -1):
                memResult = 'valid-memtrack'
            if(line.find(overflowFalseString) != -1):
                safetyResult = 'FALSE(OVERFLOW)'
            if (line.find(errorPathBeginString) != -1):
                readingErrorPath = True
            if (readingErrorPath and line.strip() == ''):
                readingErrorPath = False
    
        if (not readingErrorPath and line == ''):
            print('\nDid read empty line, but expected closing message. Wrong executable or arguments?')
            break
        
        if (line.find('Preparing to exit Ultimate with return code 0') != -1):
            print('\nExecution finished normally') 
            break
    
    return safetyResult, memResult, overapprox, ultimateOutput, errorPath


def createUltimateCall(call, arguments):
    for arg in arguments:
        if(isinstance (arg, list)):
            for subarg in arg:
                call = call + ' "' + subarg + '"'
        else:
            call = call + ' "' + arg + '"'
    return call    
    

def getSettingsFile(bitprecise, settingsSearchString):
    if bitprecise:
        print ('Using bit-precise analysis')
        settingsSearchString = settingsSearchString + '*_' + settingsFileBitprecise
    else:
        print ('Using default analysis')
        settingsSearchString = settingsSearchString + '*_' + settingsFileDefault
    settingsArgument = searchCurrentDir('*' + settingsSearchString + '*.epf')
    if settingsArgument == '' or settingsArgument == None:
        print ('No suitable settings file found using ' + settingsSearchString)
        print ('ERROR: UNSUPPORTED PROPERTY') 
        sys.exit(1)
    return settingsArgument



def parseArgs():
    # parse command line arguments
    
    if ((len(sys.argv) == 2) and (sys.argv[1] == '--version')):
        print (version)
        sys.exit(0)
    
    parser = argparse.ArgumentParser(description='Ultimate wrapper script for SVCOMP')
    parser.add_argument('--version', action='store_true')
    parser.add_argument('--full-output', action='store_true')
    parser.add_argument('spec', nargs=1, help='An property (.prp) file from SVCOMP')
    parser.add_argument('architecture', choices=['32bit', '64bit'])
    parser.add_argument('memorymodel', choices=['simple', 'precise'])
    parser.add_argument('file', nargs='+', help='All the input files')
    
    args = parser.parse_args()
  
    if (args.version):
        print(version)
        sys.exit(0)
    
    if(not args.file):
        printErr('You must specify at least one input file')
        sys.exit(1)
    
    if(len(args.file) > 2):
        printErr('You cannot specify more than 2 input files')
        sys.exit(1)
    
    cFile = None
    witness = None   
    for f in args.file:
        if not os.path.isfile(f):
            printErr('Input file ' + f + ' does not exist')
            sys.exit(1)
        if f.endswith('.graphml'):
            witness = f
        else:
            cFile = f
    
    if(cFile == None and witness != None):
        printErr("You did not specify a C file with your witness")
        sys.exit(1)
    
    propertyFileName = args.spec[0]
    if not os.path.isfile(propertyFileName):
        printErr("Property file not found at " + propertyFileName)
        sys.exit(1)
   
    return propertyFileName, args.architecture, args.file, args.full_output


def createSettingsSearchString(memDeref, memDerefMemtrack, terminationMode, overflowMode, architecture):
    settingsSearchString = ''
    if memDeref and memDerefMemtrack:
        print ('Checking for memory safety (deref-memtrack)')
        settingsSearchString = settingsFileMemSafetyDerefMemtrack
    elif memDeref:
        print ('Checking for memory safety (deref)')
        settingsSearchString = settingsFileMemSafetyDeref
    elif terminationMode:
        print ('Checking for termination')
        settingsSearchString = settingsFileTermination
    elif overflowMode:
        print ('Checking for overflows')
        settingsSearchString = settingsFileOverflow
    else:
        print ('Checking for ERROR reachability')
        settingsSearchString = settingsFileReach
    settingsSearchString = settingsSearchString + '*' + architecture
    return settingsSearchString


def createToolchainString(termmode, witnessmode):
    if termmode:
        toolchain = searchCurrentDir('*Termination.xml');
        if toolchain == '' or toolchain == None:
            print ('No suitable settings file found using *Termination.xml')
            sys.exit(1)
        return toolchain
    elif witnessmode: 
        toolchain = searchCurrentDir('*WitnessValidation.xml');
        if toolchain == '' or toolchain == None:
            print ('No suitable settings file found using **WitnessValidation.xml')
            sys.exit(1)
        return toolchain
    else:
        for root, dirs, files in os.walk('.'):
            for name in files:
                if fnmatch.fnmatch(name, '*.xml') and not fnmatch.fnmatch(name, 'artifacts.xml') and not fnmatch.fnmatch(name, '*Termination.xml') and not fnmatch.fnmatch(name, '*WitnessValidation.xml'):
                    return os.path.join(root, name)
            break
    print('No suitable toolchain file found')
    sys.exit(1)
    return 

def printErr(*objs):
    print(*objs, file=sys.stderr)

def main():
    # different modes 
    memDeref = False
    memDerefMemtrack = False
    terminationMode = False
    witnessMode = False
    overflowMode = False
    
    ultimateBin = setBinary()
    
    propertyFileName, architecture, cFile, verbose = parseArgs()
    
    propFile = open(propertyFileName, 'r')
    for line in propFile:
        if line.find('valid-deref') != -1:
            memDeref = True
        if line.find('valid-memtrack') != -1:
            memDerefMemtrack = True
        if line.find('LTL(F end)') != -1:
            terminationMode = True
        if line.find('overflow') != -1:
            overflowMode = True
    
    witnessMode = len(cFile) > 1
    
    settingsSearchString = createSettingsSearchString(memDeref, memDerefMemtrack, terminationMode, overflowMode, architecture)
    settingsArgument = getSettingsFile(False, settingsSearchString)
    
    toolchain = createToolchainString(terminationMode, witnessMode)

    # execute ultimate
    print('Version ' + version)
    ultimateCall = createUltimateCall(ultimateBin, [toolchain, cFile, "--settings", settingsArgument])
 

    # actually run Ultimate 
    safetyResult, memResult, overaprox, ultimateOutput, errorPath = runUltimate(ultimateCall, terminationMode)
    
    if(overaprox):
        # we did fail because we had to overaproximate. Lets rerun with bit-precision 
        print('Retrying with bit-precise analysis')
        settingsArgument = getSettingsFile(True, settingsSearchString)
        ultimateCall = createUltimateCall(ultimateBin, [toolchain, cFile, '--settings', settingsArgument])
        safetyResult, memResult, overaprox, ultimate2Output, errorPath = runUltimate(ultimateCall, terminationMode)
        ultimateOutput = ultimateOutput + '\n### Bit-precise run ###\n' + ultimate2Output
    
    # summarize results
    if writeUltimateOutputToFile:
        print('Writing output log to file {}'.format(outputFileName))
        outputFile = open(outputFileName, 'wb')
        outputFile.write(ultimateOutput.encode('utf-8'))
    
    if safetyResult.startswith('FALSE'):
        print('Writing human readable error path to file {}'.format(errorPathFileName))
        errOutputFile = open(errorPathFileName, 'wb')
        errOutputFile.write(errorPath.encode('utf-8'))
    
    if memDeref and safetyResult.startswith('FALSE'):
        result = 'FALSE({})'.format(memResult)
    else:
        result = safetyResult
        
    print('Result:') 
    print(result)
    if(verbose):
        print('--- Real Ultimate output ---')
        print(ultimateOutput.encode('UTF-8', 'replace'))
        
    return

if __name__ == "__main__":
    main()
