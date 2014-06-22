import sys
import subprocess

#locations of files
#ultimateBin = '/storage/stalin/trunk/source/BA_SiteRepository/target/products/CLI-E3/linux/gtk/x86_64/Ultimate'
#ultimateBin = '../../source/BA_SiteRepository/target/products/CLI-E3/linux/gtk/x86_64/Ultimate'
ultimateBin = './Ultimate'
#toolchain = './TraceAbstractionC.xml'
toolchain = './BuchiAutomizerCWithBlockEncoding.xml'
settingsFileErrorReachability = './AutomizerSvcompSafety.settings'
settingsFileMemSafety = './AutomizerSvcompMemsafety.settings'
settingsFileTermination = './BuchiAutomizerSvcomp.settings'
#special strings in ultimate output
safetyString = 'Ultimate proved your program to be correct'
unsafetyString = 'Ultimate proved your program to be incorrect'
unknownSafetyString = 'Ultimate could not prove your program'

terminationString = 'Buchi Automizer proved that your program is terminating'
notterminationString = 'Found a nonterminating execution'
unknownTerminationString = 'Buchi Automizer was unable to decide termination'
decompositionIntoModulesString = 'Buchi Automizer proved that your program is terminating  Your program was decomposed'

memDerefUltimateString = 'pointer dereference may fail'
memFreeUltimateString = 'free of unallocated memory possible'
memMemtrackUltimateString = 'not all allocated memory was freed' 
errorPathBeginString = 'Found a nonterminating execution for the following lasso shaped sequence of statements.'
errorPathEndString = 'End of lasso representation.'
memDerefResult = 'valid-deref'
memFreeResult = 'valid-free'
memMemtrackResult = 'valid-memtrack'

writeUltimateOutputToFile = True
outputFileName = './ultimateOut.txt'

#parse command line arguments
if (len(sys.argv) != 4):
	print('wrong number of arguments')
	sys.exit(0)

propertyFileName = sys.argv[1]
cFile = sys.argv[2]
errorPathFileName = sys.argv[3]

memSafetyMode = False
terminationMode = False

propFile = open(propertyFileName, 'r')
for line in propFile:
	if line.find('valid-') != -1:
		memSafetyMode = True
	if line.find('end') != -1:
		terminationMode = True

if memSafetyMode:
	print('checking for memory safety')
elif terminationMode:
	print('checking for termination')
else: 
	print('checking for ERROR reachability')
#else:
#	print('unknown property file')
#	sys.exit(0)

if (memSafetyMode):
	settingsArgument = '--settings ' + settingsFileMemSafety
elif terminationMode:
	settingsArgument = '--settings ' + settingsFileTermination
else:
	settingsArgument = '--settings ' + settingsFileErrorReachability


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
terminationResult = 'EXCEPTION'
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
	if (line.find(terminationString) != -1):
		terminationResult = 'TRUE'
	if (line.find(notterminationString) != -1):
		terminationResult = 'FALSE'
	if (line.find(unknownTerminationString) != -1):
		terminationResult = 'UNKNOWN'
	if (line.find(errorPathBeginString) != -1):
		readingErrorPath = True
	if (line.find(errorPathEndString) != -1):
		readingErrorPath = False
	if (line.find(decompositionIntoModulesString) != -1):
		print(line)
	if (line == ''):
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

if terminationResult == 'FALSE':
	print('writing output to file {}'.format(errorPathFileName))
	errOutputFile = open(errorPathFileName, 'wb')
	errOutputFile.write(errorPath.encode('utf-8'))

result = terminationResult
#if (memSafetyMode and safetyResult == 'FALSE'):
	#result = 'FALSE({})'.format(memResult)
#else:
	#result = safetyResult
print('Result:') 
print(result)
