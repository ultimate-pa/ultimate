#!/usr/bin/env python2.7

import sys
import subprocess
import os
import fnmatch
import platform

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
safetyString = 'Ultimate proved your program to be correct'
allSpecString = 'AllSpecificationsHoldResult'
unsafetyString = 'Ultimate proved your program to be incorrect'
memDerefUltimateString = 'pointer dereference may fail'
memFreeUltimateString = 'free of unallocated memory possible'
memMemtrackUltimateString = 'not all allocated memory was freed' 
errorPathBeginString = 'We found a FailurePath:'
terminationFalse = 'Found a nonterminating execution for the following lasso shaped sequence of statements'
terminationPathEnd = 'End of lasso representation.'
terminationTrue = 'TerminationAnalysisResult: Termination proven'
overflowString = 'overflow possible'


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
        line = ultimateProcess.stdout.readline().decode('utf-8')
        if readingErrorPath:
            errorPath += line
        ultimateOutput += line
        sys.stdout.write('.')
        # sys.stdout.write('Ultimate: ' + line)
        sys.stdout.flush()
        if(not overapprox and containsOverapproximationResult(line)):
            overapprox = True
        if (terminationMode):
            if (line.find(terminationTrue) != -1):
                safetyResult = 'TRUE(TERM)'
            if (line.find(terminationFalse) != -1):
                safetyResult = 'FALSE(TERM)'
                readingErrorPath = True
            if (line.find(terminationPathEnd) != -1):
                readingErrorPath = False
        else:
            if (line.find(safetyString) != -1 or line.find(allSpecString) != -1):
                safetyResult = 'TRUE'
            if (line.find(unsafetyString) != -1):
                safetyResult = 'FALSE'
            if (line.find(memDerefUltimateString) != -1):
                memResult = 'valid-deref'
            if (line.find(memFreeUltimateString) != -1):
                memResult = 'valid-free'
            if (line.find(memMemtrackUltimateString) != -1):
                memResult = 'valid-memtrack'
            if(line.find(overflowString) != -1):
                safetyResult = 'FALSE(OVERFLOW)'
            if (line.find(errorPathBeginString) != -1):
                readingErrorPath = True
            if (readingErrorPath and line.strip() == ''):
                readingErrorPath = False
    
        if (not readingErrorPath and line == ''):
            print('\nDid read empty line, but expected closing message. Wrong executable or arguments?')
            break
        
        if (line.find('Closed successfully') != -1):
            print('\nExecution finished normally') 
            break
    
    return safetyResult, memResult, overapprox, ultimateOutput, errorPath


def createUltimateCall(call, arguments):
    for arg in arguments:
        call = call + ' "' + arg + '"'
        
    return call    
    

def getSettingsFile(bitprecise, settingsSearchString):
    if bitprecise:
        print 'Using bit-precise analysis'
        settingsSearchString = settingsSearchString + '*_' + settingsFileBitprecise
    else:
        print 'Using default analysis'
        settingsSearchString = settingsSearchString + '*_' + settingsFileDefault
    settingsArgument = searchCurrentDir('*' + settingsSearchString + '*.epf')
    if settingsArgument == '' or settingsArgument == None:
        print 'No suitable settings file found using ' + settingsSearchString
        sys.exit(1)
    return settingsArgument



def parseArgs():
# parse command line arguments
    if ((len(sys.argv) == 2) and (sys.argv[1] == '--version')):
        print version
        sys.exit(0)
    if (len(sys.argv) < 5):
        print 'Wrong number of arguments: use ./Ultimate.py <propertyfile> <C file> [32bit|64bit] [simple|precise]'
        sys.exit(1)
    
    propertyFileName = sys.argv[1]
    if not os.path.isfile(propertyFileName):
        print("Property file not found at " + propertyFileName)
        sys.exit(1)
    
    cFile = sys.argv[2]
    if not os.path.isfile(cFile):
        print("Input file not found at " + cFile)
        sys.exit(1)
    
    architecture = sys.argv[3]
    if not architecture in ("32bit", "64bit"): 
        print('Architecture has to be either 32bit or 64bit')
        sys.exit(0)
    
    # we currently ignore the memory model
    memorymodel = sys.argv[4]
    if not memorymodel in ("simple", "precise"): 
        print('Memory model has to be either simple or precise')
        sys.exit(0)
    
    verbose = (len(sys.argv) > 5 and sys.argv[5] == '--full-output')
    
    return propertyFileName, architecture, cFile, verbose


def createSettingsSearchString(memDeref, memDerefMemtrack, terminationMode, overflowMode, architecture):
    settingsSearchString = ''
    if memDeref and memDerefMemtrack:
        print 'Checking for memory safety (deref-memtrack)'
        settingsSearchString = settingsFileMemSafetyDerefMemtrack
    elif memDeref:
        print 'Checking for memory safety (deref)'
        settingsSearchString = settingsFileMemSafetyDeref
    elif terminationMode:
        print 'Checking for termination'
        settingsSearchString = settingsFileTermination
    elif overflowMode:
        print 'Checking for overflows'
        settingsSearchString = settingsFileOverflow
    else:
        print 'Checking for ERROR reachability'
        settingsSearchString = settingsFileReach
    settingsSearchString = settingsSearchString + '*' + architecture
    return settingsSearchString


def createToolchainString(terminationMode):
    if terminationMode:
        return searchCurrentDir('*Termination.xml')
    else:
        for root, dirs, files in os.walk('.'):
            for name in files:
                if fnmatch.fnmatch(name, '*.xml') and not fnmatch.fnmatch(name, 'artifacts.xml') and not fnmatch.fnmatch(name, '*Termination.xml'):
                    return os.path.join(root, name)
            break
    print('No suitable toolchain file found')
    sys.exit(1)
    return 


def main():
    # different modes 
    memDeref = False
    memDerefMemtrack = False
    terminationMode = False
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
    
    settingsSearchString = createSettingsSearchString(memDeref, memDerefMemtrack, terminationMode, overflowMode, architecture)
    settingsArgument = getSettingsFile(False, settingsSearchString)
    toolchain = createToolchainString(terminationMode)

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
    
    if memDeref:
        if(safetyResult.startswith('FALSE')):
            result = 'FALSE({})'.format(memResult)
        elif safetyResult.startswith('TRUE'):
            result = 'TRUE({})'.format(memResult)
    else:
        result = safetyResult
        
    print('Result:') 
    print(result)
    if(verbose):
        print('--- Real Ultimate output ---')
        print(ultimateOutput)
        
    return

if __name__ == "__main__":
    main()
