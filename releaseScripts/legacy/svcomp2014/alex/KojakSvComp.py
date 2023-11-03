import sys
import subprocess

#locations of files
#ultimateBin = '/storage/stalin/trunk/source/BA_SiteRepository/target/products/CLI-E3/linux/gtk/x86_64/Ultimate'
#ultimateBin = '../../source/BA_SiteRepository/target/products/CLI-E3/linux/gtk/x86_64/Ultimate'
# current z3 version z3-4.3.3.f50a8b0a59ff-x64-debian-7.7.zip
ultimateBin = './Ultimate'
toolchain = './ToolchainKojakC.xml'
settingsFileErrorReachability = './AlexSVCOMPstandard'
settingsFileMemSafety = './AlexSVCOMPmemsafety'
#special strings in ultimate output
safetyString = 'Ultimate proved your program to be correct'
unsafetyString = 'Ultimate proved your program to be incorrect'
unknownSafetyString = 'Ultimate could not prove your program'
memDerefUltimateString = 'pointer dereference may fail'
memFreeUltimateString = 'free of unallocated memory possible'
memMemtrackUltimateString = 'not all allocated memory was freed' 
errorPathBeginString = '=== Start of program execution'
errorPathEndString = '=== End of program execution'
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

propFile = open(propertyFileName, 'r')
for line in propFile:
	if line.find('valid-') != -1:
		memSafetyMode = True

if memSafetyMode:
	print('checking for memory safety')
else: 
	print('checking for ERROR reachability')
#else:
#	print('unknown property file')
#	sys.exit(0)

if (memSafetyMode):
	settingsArgument = '--settings ' + settingsFileMemSafety
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
	if (line.find(errorPathEndString) != -1):
		readingErrorPath = False
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

if (memSafetyMode and safetyResult == 'FALSE'):
	result = 'FALSE({})'.format(memResult)
else:
	result = safetyResult
print('Result:') 
print(result)
