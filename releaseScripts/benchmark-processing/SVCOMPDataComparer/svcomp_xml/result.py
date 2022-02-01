from cProfile import run
class SVCOMPResult(object):
    
    benchmarkname = ""
    block = ""
    cpuCores = ""
    dateStart = None
    dateEnd = []
    generator = ""
    memlimit = ""
    name = ""
    options = []
    timelimit = ""
    tool = ""
    toolmodule = ""
    version = ""
    __runs__ = []
       
    def __str__(self, *args, **kwargs):
        output = \
        "Result:\n" + self.benchmarkname + "\n" \
        + "Block: " + self.block + "\n" \
        + "Date: " + str(self.dateStart) + "\n" \
        + "End Dates: " + ", ".join(str(dat) for dat in self.dateEnd) + "\n"
        return output
    
    def getnametorun(self, name):
        for run in self.__runs__:
            if run['name'] == name:
                return run
            
        raise ValueError("No run with name " + name + " found in the current result.")
    
    def getrunswithstatus(self, status):
        "Returns all runs with a certain status"
        
        runs = []
        for run in self.__runs__:
            if run['status'] == status:
                runs.append(run)
                
        return runs