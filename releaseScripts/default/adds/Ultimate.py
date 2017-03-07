#!/usr/bin/env python2.7

from __future__ import print_function
import sys
import subprocess
import os
import fnmatch
import platform
import argparse

version = '47e1251f'
toolname = 'wrong toolname'
writeUltimateOutputToFile = True
outputFileName = 'Ultimate.log'
errorPathFileName = 'UltimateCounterExample.errorpath'
ultimatedir = os.path.dirname(os.path.realpath(__file__))
configdir = ultimatedir

# special strings in ultimate output
unsupportedSyntaxErrorString = 'ShortDescription: Unsupported Syntax'
incorrectSyntaxErrorString = 'ShortDescription: Incorrect Syntax'
typeErrorString = 'Type Error'
witnessErrorString = 'InvalidWitnessErrorResult'
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


def getBinary():
    # currently unused because of rcp launcher bug 
    # currentPlatform = platform.system()
    #if currentPlatform == 'Windows':

    
    ultimateBin = ['java', '-Xmx12G', '-Xms1G', '-jar' , os.path.join(ultimatedir,'plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar'), '-data', '@user.home/.ultimate']
    # check if ultimate bin is there 
    # if not os.path.isfile(ultimateBin):
    #    print("Ultimate binary not found, expected " + ultimateBin)
    #    sys.exit(1)
    
    return ultimateBin


def searchConfigDir(searchstring):
    
    for root, dirs, files in os.walk(configdir):
        for name in files:
            if fnmatch.fnmatch(name, searchstring):
                return os.path.join(root, name)
        break
    print ("No suitable file found in config dir {0} using search string {1}".format(configdir,searchstring))    
    return 


def containsOverapproximationResult(line):
    triggers = [
                'Reason: overapproximation of',
                'Reason: overapproximation of bitwiseAnd',
                'Reason: overapproximation of bitwiseOr',
                'Reason: overapproximation of bitwiseXor',
                'Reason: overapproximation of shiftLeft',
                'Reason: overapproximation of shiftRight',
                'Reason: overapproximation of bitwiseComplement'
                ]
    
    for trigger in triggers:
        if line.find(trigger) != -1:
            return True
    
    return False


def runUltimate(ultimateCall, terminationMode):
    print('Calling Ultimate with: ' + " ".join(ultimateCall))
    
    try:
        ultimateProcess = subprocess.Popen(ultimateCall, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=False)
    except:
        print('Error trying to open subprocess')
        sys.exit(1)
    
    
    safetyResult = 'UNKNOWN'
    memResult = 'NONE'
    overflow = False
    readingErrorPath = False
    overapprox = False
    
    # poll the output
    ultimateOutput = ''
    errorPath = ''
    while True:
        line = ultimateProcess.stdout.readline().decode('utf-8', 'ignore')
        
        ultimateProcess.poll()
        if (ultimateProcess.returncode != None and not line):
            if (ultimateProcess.returncode == 0):
                print('\nExecution finished normally')
            else: 
                print('\nExecution finished with exit code ' + str(ultimateProcess.returncode)) 
            break
        
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
        elif (line.find(witnessErrorString) != -1):
            safetyResult = 'ERROR: INVALID WITNESS FILE'
        elif (line.find(exceptionErrorString) != -1):
            safetyResult = 'ERROR: ' + line[line.find(exceptionErrorString):]
            # hack to avoid errors with floats 
            overapprox = True           
        if (not overapprox and containsOverapproximationResult(line)):
            safetyResult = 'UNKNOWN: Overapproximated counterexample'
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
                overflow = True
                safetyResult = 'FALSE'
            if (line.find(errorPathBeginString) != -1):
                readingErrorPath = True
            if (readingErrorPath and line.strip() == ''):
                readingErrorPath = False

    return safetyResult, memResult, overflow, overapprox, ultimateOutput, errorPath


def createUltimateCall(call, arguments):
    for arg in arguments:
        if(isinstance (arg, list)):
            for subarg in flatten(arg):
                call = call + [subarg]
        else:
            call = call + [arg]
    return call 

def flatten(l):
    for el in l:
        if isinstance(el, list) and not isinstance(el, basestring) and not isinstance(el, (str, bytes)):
            for sub in flatten(el):
                yield sub
        else:
            yield el   

def createCliSettings(checkTermination, validateWitness, prop, architecture, cFile):
    if checkTermination:
        # we can neither validate nor produce witnesses in termination mode, so no additional arguments are required
        return []
    
    ret = []
    if validateWitness:
        # we need to disable hoare triple generation as workaround for an internal bug
        ret.append('--traceabstraction.compute.hoare.annotation.of.negated.interpolant.automaton,.abstraction.and.cfg')
        ret.append('false')
    else:
        # we are neither in termination nor in validation mode, so we should generate a witness and need 
        # to pass some things to the witness printer
        ret.append('--witnessprinter.graph.data.specification')
        ret.append(prop)
        ret.append('--witnessprinter.graph.data.producer')
        ret.append(toolname)
        ret.append('--witnessprinter.graph.data.architecture')
        ret.append(architecture)
        ret.append('--witnessprinter.graph.data.programhash')
        try:
            sha = subprocess.Popen(['sha1sum', cFile], stdout=subprocess.PIPE).communicate()[0]
            ret.append(sha.split()[0])
        except:
            print('Error trying to start sha1sum')
            sys.exit(1)

    return ret

def getSettingsPath(bitprecise, settingsSearchString):
    if bitprecise:
        print ('Using bit-precise analysis')
        settingsSearchString = settingsSearchString + '*_' + 'Bitvector'
    else:
        print ('Using default analysis')
        settingsSearchString = settingsSearchString + '*_' + 'Default'

    settingsArgument = searchConfigDir('*' + settingsSearchString + '*.epf')
    
    if settingsArgument == '' or settingsArgument == None:
        print ('No suitable settings file found using ' + settingsSearchString)
        print ('ERROR: UNSUPPORTED PROPERTY') 
        sys.exit(1)
    return settingsArgument


def checkFile(f):
    if not os.path.isfile(f):
        printErr('Input file ' + f + ' does not exist')
        sys.exit(1)
    return file

def parseArgs():
    # parse command line arguments
    
    if ((len(sys.argv) == 2) and (sys.argv[1] == '--version')):
        print (version)
        sys.exit(0)
    
    parser = argparse.ArgumentParser(description='Ultimate wrapper script for SVCOMP')
    parser.add_argument('--version', action='store_true', help='Print Ultimate\'s version and exit')
    parser.add_argument('--full-output', action='store_true', help='Print Ultimate\'s full output to stderr after verification ends')
    parser.add_argument('--validate', nargs=1, metavar='<file>', help='Activate witness validation mode (if supported) and specify a .graphml file as witness')
    parser.add_argument('spec', nargs=1, help='An property (.prp) file from SVCOMP')
    parser.add_argument('architecture', choices=['32bit', '64bit'], help='Choose which architecture (defined as per SV-COMP rules) should be assumed')
    parser.add_argument('file', metavar='<file>', nargs=1, help='One C file')
    
    args = parser.parse_args()
  
    if (args.version):
        print(version)
        sys.exit(0)
    
    if(not args.file):
        printErr('You must specify at least one input file')
        sys.exit(1)
    
    witness = None
    cFile = checkFile(args.file[0])
    if args.validate:
        witness = args.validate[0]
    
    if(cFile == None and witness != None):
        printErr("You did not specify a C file with your witness")
        sys.exit(1)
    
    propertyFileName = args.spec[0]
    if not os.path.isfile(propertyFileName):
        printErr("Property file not found at " + propertyFileName)
        sys.exit(1)
        
    if not args.validate and witness != None:
        printErr("You did specify a witness but not --validate")
        sys.exit(1)
   
    if args.validate and witness == None:
        printErr("You did specify --validate but no witness")
        sys.exit(1)
    if args.validate:
        return propertyFileName, args.architecture, [args.file[0], witness], args.full_output, args.validate
    else:
        return propertyFileName, args.architecture, args.file[0], args.full_output, args.validate

def createSettingsSearchString(memDeref, memDerefMemtrack, terminationMode, overflowMode, architecture):
    settingsSearchString = ''
    if memDeref and memDerefMemtrack:
        print ('Checking for memory safety (deref-memtrack)')
        settingsSearchString = 'DerefFreeMemtrack'
    elif memDeref:
        print ('Checking for memory safety (deref)')
        settingsSearchString = 'Deref'
    elif terminationMode:
        print ('Checking for termination')
        settingsSearchString = 'Termination'
    elif overflowMode:
        print ('Checking for overflows')
        settingsSearchString = 'Overflow'
    else:
        print ('Checking for ERROR reachability')
        settingsSearchString = 'Reach'
    settingsSearchString = settingsSearchString + '*' + architecture
    return settingsSearchString


def getToolchainPath(termmode, memDeref, memDerefMemtrack, overflowMode, witnessmode):
    searchString = None
    if termmode:
        searchString = '*Termination.xml'
    elif witnessmode:
        searchString = '*WitnessValidation.xml'
    elif memDeref and memDerefMemtrack:
        searchString = '*MemDerefMemtrack.xml'
    else:
        searchString = '*Reach.xml'
    
    toolchain = searchConfigDir(searchString);
    
    if toolchain == '' or toolchain == None:
        print ('No suitable toolchain file found using ' + searchString)
        sys.exit(1)
        
    return toolchain 


def printErr(*objs):
    print(*objs, file=sys.stderr)


def determineMode(propertyFileName):
    terminationMode = False
    memDeref = False
    memDerefMemtrack = False
    overflowMode = False
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
    
    return terminationMode, memDeref, memDerefMemtrack, overflowMode

def main():
    ultimateBin = getBinary()
    propertyFileName, architecture, inputFiles, verbose, validateWitness = parseArgs()
    terminationMode, memDeref, memDerefMemtrack, overflowMode = determineMode(propertyFileName)
            
    propFileStr = open(propertyFileName, 'r').read()

    toolchain = getToolchainPath(terminationMode, memDeref, memDerefMemtrack, overflowMode, validateWitness)
    settingsSearchString = createSettingsSearchString(memDeref, memDerefMemtrack, terminationMode, overflowMode, architecture)
    settingsArgument = getSettingsPath(False, settingsSearchString)
    
    # create manual settings that override settings files for witness passthrough (collecting various things) and for witness validation
    manualCliArguments = createCliSettings(terminationMode, validateWitness, propFileStr, architecture, inputFiles)

    # execute ultimate
    print('Version ' + version)
    ultimateCall = createUltimateCall(ultimateBin, ['-tc', toolchain, '-i', inputFiles, '-s', settingsArgument, manualCliArguments])
 

    # actually run Ultimate 
    safetyResult, memResult, overflow, overapprox, ultimateOutput, errorPath = runUltimate(ultimateCall, terminationMode)
    
    if(overapprox):
        # we did fail because we had to overapproximate. Lets rerun with bit-precision 
        print('Retrying with bit-precise analysis')
        settingsArgument = getSettingsPath(True, settingsSearchString)
        ultimateCall = createUltimateCall(ultimateBin, ['-tc', toolchain, '-i', inputFiles, '-s', settingsArgument, manualCliArguments])
        safetyResult, memResult, overflow, overapprox, ultimate2Output, errorPath = runUltimate(ultimateCall, terminationMode)
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
        if memDeref:
            result = 'FALSE({})'.format(memResult)
        elif overflow: 
            result = 'FALSE(OVERFLOW)'
        else: 
            result = safetyResult
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
