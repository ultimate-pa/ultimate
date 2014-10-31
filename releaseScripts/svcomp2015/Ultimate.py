import sys
import subprocess
import os
import fnmatch

# current z3 version z3-4.3.3.f50a8b0a59ff-x64-debian-7.7.zip



ultimateBin = './Ultimate'
toolchain = './Kojak.xml'
writeUltimateOutputToFile = True
outputFileName = 'Ultimate.log'
errorPathFileName = 'UltimateCounterExample.errorpath'

# various settings file strings 
settingsFileMemSafety = 'memsafety'
settingsFileTermination = 'termination'
settingsFileSimple32 = '32bit-simple'
settingsFileSimple64 = '64bit-simple'
settingsFilePrecise32 = '32bit-precise'
settingsFilePrecise64 = '64bit-precise'


#special strings in ultimate output
safetyString = 'Ultimate proved your program to be correct'
unsafetyString = 'Ultimate proved your program to be incorrect'
unknownSafetyString = 'Ultimate could not prove your program'
memDerefUltimateString = 'pointer dereference may fail'
memFreeUltimateString = 'free of unallocated memory possible'
memMemtrackUltimateString = 'not all allocated memory was freed' 
errorPathBeginString = 'We found a FailurePath:'
memDerefResult = 'valid-deref'
memFreeResult = 'valid-free'
memMemtrackResult = 'valid-memtrack'


#parse command line arguments
if (len(sys.argv) != 5):
	print('wrong number of arguments: use ./Ultimate.py <propertyfile> <C file> [32bit|64bit] [simple|precise]')
	sys.exit(0)

propertyFileName = sys.argv[1]
cFile = sys.argv[2]
architecture = sys.argv[3]
memorymodel = sys.argv[4]

memSafetyMode = False
terminationMode = False

propFile = open(propertyFileName, 'r')
for line in propFile:
	if line.find('valid-') != -1:
		memSafetyMode = True
	if line.find('LTL(F end)') != -1:
		terminationMode = True

settingsSearchString = ''

if memSafetyMode:
	print('checking for memory safety')
	settingsSearchString = settingsFileMemSafety
elif terminationMode: 
	print('checking for termination')
	settingsSearchString = settingsFileTermination
else: 
	print('checking for ERROR reachability')
	if architecture in ("32bit", "64bit"): 
		settingsSearchString = architecture
	else:
		print('architecture has to be either 32bit or 64bit')
		sys.exit(0)
	if memorymodel in ("simple", "precise"): 
		settingsSearchString = settingsSearchString + '-' + memorymodel
	else:
		print('memorymodel has to be either simple or precise')
		sys.exit(0)

settingsArgument = ''
for root, dirs, files in os.walk('./'):
	for name in files:
		if fnmatch.fnmatch(name, '*' + settingsSearchString + '*.epf'):
			settingsArgument = '--settings '+os.path.join(root, name)
			break

#execute ultimate
ultimateCall = ultimateBin 
ultimateCall += ' ' + toolchain  
ultimateCall += ' ' +  cFile
ultimateCall += ' ' +  settingsArgument

#print('Calling Ultimate with: ' + ultimateCall)

try:
	ultimateProcess = subprocess.Popen(ultimateCall, stdin=subprocess.PIPE, stdout = subprocess.PIPE, stderr = subprocess.PIPE, shell=True)
except:
	print('error trying to open subprocess')
	sys.exit(0)


safetyResult = 'UNKNOWN'
memResult = 'NONE'
readingErrorPath = False

#poll the output
ultimateOutput = ''
errorPath = ''
while True:
	line = ultimateProcess.stdout.readline().decode('utf-8')
	if readingErrorPath:
		errorPath += line
	ultimateOutput += line
	sys.stdout.write('.')
	#sys.stdout.write('Ultimate: ' + line)
	sys.stdout.flush()
	if (line.find(safetyString) != -1):
		safetyResult = 'TRUE'
	if (line.find(unsafetyString) != -1):
		safetyResult = 'FALSE'
	if (line.find(unknownSafetyString) != -1):
		safetyResult = 'UNKNOWN'
	if (line.find(memDerefUltimateString) != -1):
		memResult = memDerefResult
	if (line.find(memFreeUltimateString) != -1):
		memResult = memFreeResult
	if (line.find(memMemtrackUltimateString) != -1):
		memResult = memMemtrackResult
	if (line.find(errorPathBeginString) != -1):
		readingErrorPath = True
	if (readingErrorPath and line == ''):
		readingErrorPath = False
	if (not readingErrorPath and line == ''):
		print('wrong executable or arguments?')
		break
	if (line.find('Closed successfully') != -1):
		print('\nexecution finished normally') 
		break

#summarize results
if writeUltimateOutputToFile:
	print('writing output to file {}'.format(outputFileName))
	outputFile = open(outputFileName, 'wb')
	outputFile.write(ultimateOutput.encode('utf-8'))

if safetyResult == 'FALSE':
	print('writing output to file {}'.format(errorPathFileName))
	errOutputFile = open(errorPathFileName, 'wb')
	errOutputFile.write(errorPath.encode('utf-8'))

if (memSafetyMode and safetyResult == 'FALSE'):
	result = 'FALSE({})'.format(memResult)
else:
	result = safetyResult
print('Result:') 
print(result)
