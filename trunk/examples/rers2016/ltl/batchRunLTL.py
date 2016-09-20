import time, os, subprocess, sys 

problems = [1]
ltlProblemsDir = ".\\"
logdir = ".\\logdir"
tempFiles = []
utlimatePath = ["Ultimate.exe"]
ultimateParams = ["-tc",
                  "LTLAutomizerC.xml",
                  "--ltl2aut.command.line.string.$1.will.be.replaced.with.the.property=\"!($1)\"",
                  "--rcfgbuilder.size.of.a.code.block=SingleStatement"]                  

def batchRunLTL():
    for problem in problems:
        #get ltl formulas from ltlfile
        prefix = os.path.join( ltlProblemsDir , "Problem") + str(problem)
        ltlFormulas = extractProperties(prefix + "ltl-converted.txt")
        probLogDir = logdir+str(problem)
        try:
            os.stat(probLogDir)
        except:
            os.mkdir(probLogDir)    
        
        for i in range(0,100):
            #splice  c prgram and ltl formula
            tempFile = getTemporaryCFile(i, prefix, ltlFormulas[i])
        
            #execute ultimate with ltl file 
            
            try:
                print("checking:" + tempFile)
                startParams = utlimatePath + ultimateParams + ["-i",tempFile]
                print(startParams)
                log = open(os.path.join(probLogDir,"log"+str(problem)+"_"+str(i)),'w+')
                #log.write(ltlFormulas[i])
                process = subprocess.Popen(startParams ,shell=True, stdout=log)
                log.close()
                
                #TODO: or timeout
                while process.poll() is None:
                    print(".", end=" ")
                    sys.stdout.flush()
                    time.sleep(1)
            #process.terminate()
            except None as e:
                print(e)
            finally:
                print(" ")
                log.close()
                if (process in vars() and process.poll() is None): 
                    process.kill()
                
        cleanup()
        
def getTemporaryCFile(i, prefix, ltlFormula):
    annotation = "//@ ltl invariant constraint%s:"%(i)
    
    cFile = open(prefix + "_bat.c").readlines()
    cFile.insert(5,annotation + ltlFormula + ";\n")
    tempFilename = os.path.join(ltlProblemsDir , "temp" + str(i) + ".c")
    tempFiles.append(tempFilename)
    tempFile = open(tempFilename, "w+")
    tempFile.writelines(cFile)
    tempFile.close()
    return tempFilename

def cleanup():
    for tempFile in tempFiles:
        os.remove(tempFile)
    
def extractProperties(propertyFile):
    ltlFile = open(propertyFile).readlines()[2:]
    ltlFormulas = []
    for i in range(len(ltlFile)):
        if ltlFile[i].startswith("#"):
            ltlFormulas.append(ltlFile[i+1].strip())
            #print(ltlFile[i+1])
    assert(len(ltlFormulas) == 100)
    return ltlFormulas



if __name__ == '__main__':
    batchRunLTL()
    input("Press play on tape")