import sys
import subprocess

#locations of files
ultimateBin = './Ultimate'
toolchain = 'TraceAbstractionC.xml'
settingsFileErrorReachability = 'AutomizerSvcomp.settings'
settingsFileMemSafety = 'AutomizerSvcomp.settings'
#special strings in ultimate output
safetyString = 'Ultimate proved your program to be correct'
unsafetyString = 'Ultimate proved your program to be incorrect'
unknownSafetyString = 'Ultimate could not prove your program'
ultimateValidDeref = 'pointer dereference may fail'
ultimateValidFree = 'free of unallocated memory possible'
ultimateValidMemtrack = 'not all allocated memory was freed' 

#strings for SV-COMP output
svcompValidDeref = 'valid-deref'
svcompValidFree = 'valid-free'
svcompValidMemtrack = 'valid-memtrack' 

#parse command line arguments
if (len(sys.argv) != 4):
	print('wrong number of arguments')
	sys.exit(0)

propertyFile = sys.argv[1]
cFile = sys.argv[2]
outputFileName = sys.argv[3]

memSafetyMode = False

if (propertyFile.endswith('PropertyMemSafety.prp')):
	print('checking for memory safety')
	memSafetyMode = True
elif (propertyFile.endswith('PropertyERROR.prp')):
	print('checking for ERROR reachability')
	memSafetyMode = False
else:
	print('unknown property file')
	sys.exit(0)

if (memSafetyMode):
	settingsArgument = '--settings ' + settingsFileMemSafety
else:
	settingsArgument = '--settings ' + settingsFileErrorReachability



#execute ultimate
ultimateCall = ultimateBin 
ultimateCall += ' ' + toolchain  
ultimateCall += ' ' +  cFile
ultimateCall += ' ' +  settingsArgument
print(ultimateCall)

ultimateProcess = subprocess.Popen(ultimateCall, stdin=subprocess.PIPE, stdout = subprocess.PIPE, stderr = subprocess.PIPE, shell=True)

safetyResult = 'UNKNOWN'
memResult = 'NONE'

#poll the output
ultimateOutput = ''
while True:
	line = ultimateProcess.stdout.readline()
	ultimateOutput += line
	sys.stdout.write('.')
	#print(line)
	if (line.find(safetyString) != -1):
		safetyResult = 'TRUE'
	if (line.find(unsafetyString) != -1):
		safetyResult = 'FALSE'
	if (line.find(unknownSafetyString) != -1):
		safetyResult = 'UNKNOWN'
	if (line.find(ultimateValidDeref) != -1):
		memResult = 'MEMDEREF'
	if (line.find(ultimateValidFree) != -1):
		memResult = 'MEMFREE'
	if (line.find(ultimateValidMemtrack) != -1):
		memResult = 'MEMLEAK'

	if (line.find('Closed successfully') != -1):
		break

#summarize results
if safetyResult == 'FALSE':
	outputFile = open(outputFileName, 'w')
	outputFile.write(ultimateOutput) 
	
print('\nexecution finished normally') 
print('Result:') 
print(safetyResult)
print('Memsafety Result:')
print(memResult)
