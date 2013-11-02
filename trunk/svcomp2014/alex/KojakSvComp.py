import sys
import subprocess

#locations of files
ultimateBin = '/storage/stalin/trunk/source/BA_SiteRepository/target/products/CLI-E3/linux/gtk/x86_64/Ultimate'
toolchain = '/storage/stalin/trunk/examples/toolchains/TraceAbstractionC.xml'
settingsFileErrorReachability = '/storage/stalin/trunk/examples/settings/AutomizerSvcomp.settings'
settingsFileMemSafety = '/storage/stalin/trunk/examples/settings/AutomizerSvcomp.settings'
#special strings in ultimate output
safetyString = 'Ultimate proved your program to be correct'
unsafetyString = 'Ultimate proved your program to be incorrect'
unknownSafetyString = 'Ultimate could not prove your program'
memDerefUltimateString = 'pointer dereference may fail'
memFreeUltimateString = 'free of unallocated memory possible'
memMemtrackUltimateString = 'not all allocated memory was freed' 
memDerefResult = 'valid-deref'
memFreeResult = 'valid-free'
memMemtrackResult = 'valid-memtrack'


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

#print('Calling Ultimate with: ' + ultimateCall)

try:
	ultimateProcess = subprocess.Popen(ultimateCall, stdin=subprocess.PIPE, stdout = subprocess.PIPE, stderr = subprocess.PIPE, shell=True)
except:
	print('error trying to open subprocess')
	sys.exit(0)


safetyResult = 'UNKNOWN'
memResult = 'NONE'

#poll the output
ultimateOutput = ''
while True:
	line = ultimateProcess.stdout.readline().decode('utf-8')
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
	if (line == ''):
		print('wrong executable or arguments?')
		break
	if (line.find('Closed successfully') != -1):
		print('\nexecution finished normally') 
		break

#summarize results
if safetyResult == 'FALSE':
	print('writing output to file {}'.format(outputFileName))
	outputFile = open(outputFileName, 'w')
	outputFile.write(ultimateOutput) 
	
if (memSafetyMode and safetyResult == 'FALSE'):
	result = 'FALSE({})'.format(memResult)
else:
	result = safetyResult
print('Result:') 
print(result)
