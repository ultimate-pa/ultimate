import os
import argparse

INCLUDETESTING = False

def replaceApBraces(line):
    """ replace AP(...) with "..." in ltl string"""
    stack = []
    line = line.replace("AP(","\"")
    line = list(line)
    i = 0
    for char in list(line):
        if char == "(":
            stack.append(char)
        if char == "\"":
            stack.append(char)
        if char == ")":#
            o = stack.pop()
            if o == "\"":
                line[i] = "\""
        i+=1
    return "".join(line)

def splitFile(file, fileName, targetDir):
    newCFile = open(os.path.join(targetDir, fileName ),"w+")
    newLTLFile = open(os.path.join(targetDir, fileName[0:-2]+".ltl"),"w+")
    useful = False
    
    for line in file:
        if (line.startswith("//#Unsafe") or line.startswith("//#Safe")) and INCLUDETESTING:
            newLTLFile.write(line) 
        elif line.startswith("//@ ltl invariant"):
            line = line.split(":")[1]
            line = str(line).replace(";","").strip()
            line = replaceApBraces(line)
            useful = True
            newLTLFile.write(line+ "\n") 
        else:
            newCFile.write(line)
            
    if (not useful):
        print("No LTL-invariant in file %s"%(fileName))
    newCFile.close()
    newLTLFile.close()
        
    
def convertDirectory(sourceDir, targetDir):
    try: 
        os.stat(targetDir)
    except:
        os.mkdir(targetDir)

    for fileName in os.listdir(sourceDir):
        if fileName.endswith(".c"): 
            file = open(os.path.join(sourceDir,fileName))
            splitFile(file, fileName, targetDir)
            
        

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Convert c file with ACSL-LTL annotations to C file and LTL file')
    parser.add_argument("source", help="directory with .c files containing ltl-acsl",type=str)
    parser.add_argument("target", help="target dir for .c and .ltl files",type=str)
    parser.add_argument("-r", "--resultInfo", help="include //#Safe and //#Unsafe information in LTL files", action="store_true")
    args = parser.parse_args()
    if args.resultInfo:
        INCLUDETESTING = True
    
    convertDirectory(args.source, args.target)