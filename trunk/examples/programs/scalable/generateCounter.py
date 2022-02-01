import sys

bitCount = 8
correct = 1

if(len(sys.argv) > 1):
	bitCount = int(sys.argv[1])
	if(len(sys.argv) > 2):
		correct = int(sys.argv[2])


program = "procedure Counter () \n{\n"

def genIfs(counter):
	if(counter == 0):
		return ""
	else:
		curX = "x" + str(bitCount - counter)
		progPart = "if ( " + curX + " == 0) { " + curX + " := 1; }\n"
		progPart += "else {\n"
		progPart += curX + " := 0;\n"
		progPart += genIfs(counter -1)
		progPart += "}\n"
		return progPart

#variable declaration
program += "var "
for i in range(bitCount-1):
	program += "x"+ str(i) + ", "
program += "x" + str(bitCount - 1) + " : int;\n"

program += "\n"

#variable initialisation
for i in range(bitCount):
	program += "x"+str(i) + " := 0;\n"

program += "\n"

#the counting
program += "while(x"+ str(bitCount - 1) + " == 0) {\n"

program += genIfs(bitCount)

program += "}\n"

#the assertion
program += "assert ("
for i in range(bitCount-1):
	program += "x"+str(i) + " == 0 && "
if(correct):
	program += "x" + str(bitCount - 1) + " == 1);\n"
else:
	program += "x" + str(bitCount - 1) + " == 0);\n"

program += "\n"

program += "}\n"

if(correct):
	fileName = str(bitCount) + "bitCounter-correct.bpl"
else:
	fileName = str(bitCount) + "bitCounter-incorrect.bpl"

outFile = open(fileName, "wt")
outFile.write(program)
outFile.close()