import os
import argparse

INCLUDE_RESULT_ULTIMATE_ANNOTATION = False
MAKE_SVCOMP_FILE_FORMAT = False 

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
    propertyFileContent = ""
    cFileContent = ""
    ltlInvarFound = False
    resultInfoFound = False
    
    for line in file:
        if (line.startswith("//#Unsafe") or line.startswith("//#Safe")):
            resultSafe = parseResultInfo(line)
            resultInfoFound = True
            if INCLUDE_RESULT_ULTIMATE_ANNOTATION:
                 propertyFileContent += line 
        elif line.strip().startswith("//@ ltl invariant"):
            ltl = getPlainLtlFomAcsl(line)
            if MAKE_SVCOMP_FILE_FORMAT:
                ltl = getSvcompCheckLine(ltl)
                ltl = getLtlWithNonBracketOperators(ltl)
            ltlInvarFound = True
            propertyFileContent += ltl + "\n" 
        else:
            cFileContent += line

    if (not ltlInvarFound):
        print("No LTL-invariant in file %s"%(fileName))
        return
    if (not resultInfoFound and (INCLUDE_RESULT_ULTIMATE_ANNOTATION or MAKE_SVCOMP_FILE_FORMAT)):
        print("No result annotation found in file: %s"%(fileName))
        return
    fileNameWithNoExt = os.path.splitext(fileName)[0]
    cFilePath = os.path.join(targetDir, fileNameWithNoExt + getResultSuffix(resultSafe) + ".c")
    newCFile = open(cFilePath,"w+")
    ltlFilePath = os.path.join(targetDir, fileNameWithNoExt + getResultSuffix(resultSafe) + getPropFileExt())
    newLTLFile = open(ltlFilePath,"w+")
    newCFile.write(cFileContent)
    newLTLFile.write(propertyFileContent)
    newCFile.close()
    newLTLFile.close()
        
    
def convertFilesInDirectory(sourceDir, targetDir):
    try: 
        os.stat(targetDir)
    except:
        os.mkdir(targetDir)

    for fileName in os.listdir(sourceDir):
        if fileName.endswith(".c"): 
            file = open(os.path.join(sourceDir,fileName))
            splitFile(file, fileName, targetDir)
     
def getPlainLtlFomAcsl(line):
    line = line.split(":")[1]
    line = str(line).replace(";","").strip()
    line = replaceApBraces(line)
    return line
    
def getLtlWithNonBracketOperators(ltlFormula):
    ltlFormula = ltlFormula.replace("[]", "G")
    ltlFormula = ltlFormula.replace("<>", "F")
    return ltlFormula
    
def parseResultInfo(resultInfo):
    if "//#Safe" in resultInfo:
        return True
    else:
        return False
    
def getResultSuffix(resultSafe):
    if MAKE_SVCOMP_FILE_FORMAT:
        if resultSafe:
            return "_true-valid-ltl"
        else:
            return "_false-valid-ltl"

def getPropFileExt():
    if MAKE_SVCOMP_FILE_FORMAT:
        return ".prp"
    else:
        return ".ltl"
        
def getSvcompCheckLine(ltlFormula):
    return "CHECK( init(main()), LTL( %s ) )"%ltlFormula
        
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Convert c file with ACSL-LTL annotations to C file and LTL file')
    parser.add_argument("source", help="directory with .c files containing ltl-acsl",type=str)
    parser.add_argument("target", help="target dir for .c and .ltl files",type=str)
    parser.add_argument("-r", "--resultInfo", help="include //#Safe and //#Unsafe annotations in LTL files", action="store_true", default= False)
    parser.add_argument("-s", "--svCompFormat", help="append SVComp file endings \"-(false|true)-valid-ltl.prp\" and CHECK annotation (use this to prepare svcomp ltl benchmarks)", action="store_true",default= False)
    args = parser.parse_args()
    INCLUDE_RESULT_ULTIMATE_ANNOTATION = args.resultInfo
    MAKE_SVCOMP_FILE_FORMAT = args.svCompFormat
    
    convertFilesInDirectory(args.source, args.target)