from outputter import Outputter
from svcomp_xml.logfile_extractor import LogFileExtractor


class Output(object):
    "Class to generate output in different formats"

    def __init__(self, outputFileName):
        "Initializes the Output"
        
        if not outputFileName or outputFileName == "":
            printToFile = False
        else:
            printToFile = True

        self.__outputter__ = Outputter(printToFile, outputFileName)

    def __printPreamble__(self, resultKeys):
        "Prints the preamble to the console"
        print "Analyzed " + str(len(resultKeys)) + " file" + ("s" if len(resultKeys) != 1 else "") + "."
        
    def __finish__(self):
        self.__outputter__.close()

    def printResult(self, result, unsounds, baseTool, compareTool, printOutputLinks, benchmarksPrefix, displayUnsounds):
        "Prints the results depending on the set parameters"
        
        self.__outputter__.writeLine("Analyzed " + str(len(result.keys())) + " file" + ("s" if len(result.keys()) != 1 else "") + ".")
        self.__outputter__.writeLine("The following differences of " + str(baseTool) + " from the comparison tool " + str(compareTool) + " were identified:\n") 
        
        firstLevel = "   "
        secondLevel = "      "
        thirdLevel = "         "
        
        for outfile, res in result.iteritems():
            self.__outputter__.writeLine(str(outfile) + ":")
            
            for baseStatus, rest in res.iteritems():
                for compareStatus, fileResults in rest.iteritems():
                    self.__outputter__.writeLine(str(firstLevel) + str(baseTool) + " result \"" + str(baseStatus) + "\" and " + compareTool + " result \"" + compareStatus + "\":")
                    
                    for fileResult in fileResults:
                        self.__outputter__.writeLine(secondLevel + str(benchmarksPrefix) + str(fileResult[0]))
                    
                        if printOutputLinks:
                            self.__outputter__.writeLine(thirdLevel + "Log for " + str(baseTool) + ":\t" + str(fileResult[1]))
                            self.__outputter__.writeLine(thirdLevel + "Log for " + str(compareTool) + ":\t" + str(fileResult[2]))
        
        if displayUnsounds:
            self.__outputter__.writeLine("\nThe following unsound results were produced by " + baseTool + ":\n")
            for outfile, res in unsounds.iteritems():
                self.__outputter__.writeLine(str(outfile) + ":")
                
                lastResult = ""
                
                for resultType, fileStatuses in res.iteritems():
                    if resultType != lastResult:
                        self.__outputter__.writeLine(str(firstLevel) + str(resultType) + ":")
                    
                    lastResult = resultType
                    
                    for filename, logurl in fileStatuses:
                        self.__outputter__.writeLine(str(secondLevel) + str(filename))
                    
                        if printOutputLinks:
                            self.__outputter__.writeLine(str(thirdLevel) + "Log: " + str(logurl))
            
        self.__finish__()
        
        
    def printUltimateResult(self, result, unsounds, baseTool, compareTool, printOutputLinks, benchmarksPrefix, displayUnsounds):
        "Prints the results in Ultimate's test suite format"
        
        self.__printPreamble__(result.keys())
        
        self.__outputter__.writeLine("// Differences between " + str(baseTool) + " and " + str(compareTool))
        
        for outfile, res in result.iteritems():
            self.__outputter__.writeLine("// " + str(outfile))
            
            for baseStatus, rest in res.iteritems():
                for compareStatus, fileResults in rest.iteritems():
                    self.__outputter__.writeLine("\n// ****** " + str(baseTool) + ": \"" + str(baseStatus) + "\", " + compareTool + ": \"" + str(compareStatus) + "\" ******")
            
                    for fileResult in fileResults:
                        if printOutputLinks:
                            self.__outputter__.writeLine("// " + str(baseTool) + ": " + str(fileResult[1]))
                            self.__outputter__.writeLine("// " + str(compareTool) + ": " + str(fileResult[2]))
                    
                        self.__outputter__.writeLine("\"" + str(benchmarksPrefix) + str(fileResult[0]) + "\",")
        
        if displayUnsounds:
            self.__outputter__.writeLine("\n// Unsoundnesses:")
            for outfile, res in unsounds.iteritems():
                self.__outputter__.writeLine("// " + str(outfile))
                
                lastResult = ""
                
                for resultType, fileStatuses in res.iteritems():
                    if resultType != lastResult:
                        self.__outputter__.writeLine("// " + str(resultType))
                    
                    lastResult = resultType
                    
                    for fileName, logUrl in fileStatuses:
                        self.__outputter__.writeLine("\"" + str(benchmarksPrefix) + str(fileName) + "\",")
                    
                        if printOutputLinks:
                            self.__outputter__.writeLine("// " + str(logUrl))
        
        self.__finish__()
    
    def printUltimateResultWithSettings(self, result, unsounds, baseTool, compareTool, printOutputLinks, comparisonOutput, benchmarksPrefix, year, displayUnsounds):
        "Prints the results in Ultimate's test suite format and adds the corresponding settings file"
        
        self.__printPreamble__(result.keys())
        self.__outputter__.writeLine("// Differences between " + str(baseTool) + " and " + str(compareTool))
        
        settings = {}
        
        for outfile, res in result.iteritems():
            self.__outputter__.writeLine("// " + str(outfile))

            for baseStatus, rest in res.iteritems():
                for compareStatus, fileResults in rest.iteritems():
                    self.__outputter__.writeLine("\n// ****** " + str(baseTool) + ": \"" + str(baseStatus) + "\", " + compareTool + ": \"" + str(compareStatus) + "\" ******")
                    
                    for fileResult in fileResults:
                        if printOutputLinks:
                            self.__outputter__.writeLine("// " + str(baseTool) + ": " + str(fileResult[1]))
                            self.__outputter__.writeLine("// " + str(compareTool) + ": " + str(fileResult[2]))
                    
                        baseLog = LogFileExtractor(fileResult[1])
                        baseSettings = baseLog.getSettings()
                        
                        if fileResult[0] in settings:
                            raise ValueError("Settings for file " + fileResult[0] + " already present.")
                    
                        settings[fileResult[0]] = baseSettings
                    
                        if comparisonOutput:
                            compareLog = LogFileExtractor(fileResult[2])
                            compareSettings = compareLog.getSettings()
                    
                        if len(baseSettings) > 1:
                            self.__outputter__.writeLine("// Multiple calls to " + str(baseTool) + " with different settings were performed")
                        
                    
                        for toolchain, setFile in baseSettings:
                            if toolchain.startswith("No suitable toolchain"):
                                self.__outputter__.writeLine("// *** " + toolchain)
                                self.__outputter__.writeLine("// *** File: " + str(fileResult[0]))
                                continue
                        
                            if len(baseSettings) > 1:
                                self.__outputter__.write("   ")

                            self.__outputter__.writeLine("new Triple<>(\"" + toolchain + "\",")
                            if len(baseSettings) > 1:
                                self.__outputter__.write("   ")

                            self.__outputter__.writeLine("             \"svcomp" + str(year) + "/" + setFile + "\",")

                            if len(baseSettings) > 1:
                                self.__outputter__.write("   ")
                        
                            self.__outputter__.writeLine("             \"" + str(benchmarksPrefix) + str(fileResult[0]) + "\"),")
                    
                        if len(baseSettings) > 1:
                            self.__outputter__.writeLine("// End of multiple calls of " + str(baseTool))
                        
                        if comparisonOutput:
                            self.__outputter__.writeLine("// Comparison tool " + str(compareTool) + " results")
                        
                            if len(compareSettings) > 1:
                                self.__outputter__.writeLine("// Multiple calls to " + str(compareTool) + " with different settings were performed")
                        
                            for toolchain, setFile in compareSettings:
                                if len(compareSettings) > 1:
                                    self.__outputter__.write("   ")
                                
                                self.__outputter__.writeLine("new Triple<>(\"" + toolchain + "\",")
                                
                                if len(compareSettings) > 1:
                                    self.__outputter__.write("   ")
                                
                                self.__outputter__.writeLine("             \"svcomp" + str(year) + "/" + setFile + "\",")
                                
                                if len(compareSettings) > 1:
                                    self.__outputter__.write("   ")

                                self.__outputter__.writeLine("             \"" + str(benchmarksPrefix) + str(fileResult[0]) + "\"),")
                            
                            if len(compareSettings) > 1:
                                self.__outputter__.writeLine("// End of multiple calls of " + str(compareTool))
                            
                            self.__outputter__.writeLine("")
            
        if displayUnsounds:
            self.__outputter__.writeLine("\n// Unsoundnesses:\n")
            
            for outfile, res in unsounds.iteritems():
                self.__outputter__.writeLine("// " + str(outfile))
                
                lastResult = ""
                
                for resultType, fileStatuses in res.iteritems():
                    for fileStatus in fileStatuses:
                        if resultType != lastResult:
                            self.__outputter__.writeLine("// " + str(resultType))
                        
                        lastResult = resultType
                        
                        for fileName, logUrl in fileStatuses:
                            if fileName not in settings:
                                log = LogFileExtractor(logUrl)
                                setting = log.getSettings()
                                settings[fileName] = setting
                            
                            currentSettings = settings[fileName]
                            if len(currentSettings) > 1:
                                self.__outputter__.writeLine("// Multiple calls to " + str(baseTool) + " with different settings were performed")
                            
                            for toolchain, setFile in currentSettings:
                                if toolchain.startswith("No suitable toolchain"):
                                    self.__outputter__.writeLine("// *** " + toolchain)
                                    self.__outputter__.writeLine("// *** File: " + str(fileStatus[1]))
                                    continue
                            
                                if len(currentSettings) > 1:
                                    self.__outputter__.write("   ")
                                    
                                self.__outputter__.writeLine("new Triple<>(\"" + toolchain + "\",")
                                
                                if len(currentSettings) > 1:
                                    self.__outputter__.write("   ")
                                
                                self.__outputter__.writeLine("             \"svcomp" + str(year) + "/" + setFile + "\",")

                                if len(currentSettings) > 1:
                                    self.__outputter__.write("   ")
                                
                                self.__outputter__.writeLine("             \"" + str(benchmarksPrefix) + str(fileStatus[1]) + "\"),")
                            
                                if len(currentSettings) > 1:
                                    self.__outputter__.writeLine("// End of multiple calls of " + str(baseTool))
                                    
        self.__finish__()