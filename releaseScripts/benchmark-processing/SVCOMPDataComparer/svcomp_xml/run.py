import collections

class SVCOMPRun(collections.MutableMapping):
    
    def __init__(self, logurlbase):
        self.__logurlbase__ = logurlbase
        self.__dictionary__ = {
            'files' : [],
            'name' : "",
            'options' : "",
            'name' : "",
            'options' : "",
            'properties' : "",
                
            # Column values
            'status' : "",
            'cputime' : "",
            'walltime' : "",
            'memUsage' : "",
            'cpuenergy' : "",
            'host' : "",
                
            # Witness 1
            'wit1_status' : "",
            'wit1_cputime' : "",
            'wit1_walltime' : "",
            'wit1_memUsage' : "",
            'wit1_cpuenergy' : "",
            'wit1_host' : "",
            # Witness 1 Hidden
            'wit1_category' : "",
            'wit1_exitcode' : "",
            'wit1_exitsignal' : "",
            'wit1_terminationreason' : "",
            'wit1_returnvalue' : "",
            'wit1_cpuenergy-pkg0' : "",
            'wit1_cpuenergy-pkg0-dram' : "",
            'wit1_cpuenergy-pkg0-core' : "",
            'wit1_cpuenergy-pkg0-uncore' : "",
            'wit1_cputime-cpu0' : "",
            'wit1_cputime-cpu1' : "",
            'wit1_cputime-cpu2' : "",
            'wit1_cputime-cpu3' : "",
            'wit1_cputime-cpu4' : "",
            'wit1_cputime-cpu5' : "",
            'wit1_cputime-cpu6' : "",
            'wit1_cputime-cpu7' : "",
            'wit1_blkio-write' : "",
            'wit1_blkio-read' : "",
            'wit1_vcloud-newEnvironment' : "",
            'wit1_vcloud-additionalEnvironment' : "",
            'wit1_vcloud-outerwalltime' : "",
            'wit1_vcloud-memoryLimit' : "",
            'wit1_vcloud-memoryNodes' : "",
            'wit1_vcloud-memoryNodesAllocation' : "",
            'wit1_vcloud-cpuCores' : "",
            'wit1_vcloud-cpuCoresDetails' : "",
            'wit1_vcloud-debug' : "",
            'wit1_vcloud-maxLogFileSize' : "",
                
            # Witness 2
            'wit2_status' : "",
            'wit2_cputime' : "",
            'wit2_walltime' : "",
            'wit2_memUsage' : "",
            'wit2_cpuenergy' : "",
            'wit2_host' : "",
            # Witness 2 Hidden
            'wit2_category' : "",
            'wit2_exitcode' : "",
            'wit2_exitsignal' : "",
            'wit2_terminationreason' : "",
            'wit2_returnvalue' : "",
            'wit2_cpuenergy-pkg0' : "",
            'wit2_cpuenergy-pkg0-dram' : "",
            'wit2_cpuenergy-pkg0-core' : "",
            'wit2_cpuenergy-pkg0-uncore' : "",
            'wit2_cputime-cpu0' : "",
            'wit2_cputime-cpu1' : "",
            'wit2_cputime-cpu2' : "",
            'wit2_cputime-cpu3' : "",
            'wit2_cputime-cpu4' : "",
            'wit2_cputime-cpu5' : "",
            'wit2_cputime-cpu6' : "",
            'wit2_cputime-cpu7' : "",
            'wit2_blkio-write' : "",
            'wit2_blkio-read' : "",
            'wit2_vcloud-newEnvironment' : "",
            'wit2_vcloud-additionalEnvironment' : "",
            'wit2_vcloud-outerwalltime' : "",
            'wit2_vcloud-memoryLimit' : "",
            'wit2_vcloud-memoryNodes' : "",
            'wit2_vcloud-memoryNodesAllocation' : "",
            'wit2_vcloud-cpuCores' : "",
            'wit2_vcloud-cpuCoresDetails' : "",
            'wit2_vcloud-debug' : "",
            'wit2_vcloud-maxLogFileSize' : "",
            
            # Witness 3
            'wit3_status' : "",
            'wit3_cputime' : "",
            'wit3_walltime' : "",
            'wit3_memUsage' : "",
            'wit3_cpuenergy' : "",
            'wit3_host' : "",
            # Witness 3 Hidden
            'wit3_category' : "",
            'wit3_exitcode' : "",
            'wit3_exitsignal' : "",
            'wit3_terminationreason' : "",
            'wit3_returnvalue' : "",
            'wit3_cpuenergy-pkg0' : "",
            'wit3_cpuenergy-pkg0-dram' : "",
            'wit3_cpuenergy-pkg0-core' : "",
            'wit3_cpuenergy-pkg0-uncore' : "",
            'wit3_cputime-cpu0' : "",
            'wit3_cputime-cpu1' : "",
            'wit3_cputime-cpu2' : "",
            'wit3_cputime-cpu3' : "",
            'wit3_cputime-cpu4' : "",
            'wit3_cputime-cpu5' : "",
            'wit3_cputime-cpu6' : "",
            'wit3_cputime-cpu7' : "",
            'wit3_blkio-write' : "",
            'wit3_blkio-read' : "",
            'wit3_vcloud-newEnvironment' : "",
            'wit3_vcloud-additionalEnvironment' : "",
            'wit3_vcloud-outerwalltime' : "",
            'wit3_vcloud-memoryLimit' : "",
            'wit3_vcloud-memoryNodes' : "",
            'wit3_vcloud-memoryNodesAllocation' : "",
            'wit3_vcloud-cpuCores' : "",
            'wit3_vcloud-cpuCoresDetails' : "",
            'wit3_vcloud-debug' : "",
            'wit3_vcloud-maxLogFileSize' : "",

            # Witness 4
            'wit4_status' : "",
            'wit4_cputime' : "",
            'wit4_walltime' : "",
            'wit4_memUsage' : "",
            'wit4_cpuenergy' : "",
            'wit4_host' : "",
            # Witness 4 Hidden
            'wit4_category' : "",
            'wit4_exitcode' : "",
            'wit4_exitsignal' : "",
            'wit4_terminationreason' : "",
            'wit4_returnvalue' : "",
            'wit4_cpuenergy-pkg0' : "",
            'wit4_cpuenergy-pkg0-dram' : "",
            'wit4_cpuenergy-pkg0-core' : "",
            'wit4_cpuenergy-pkg0-uncore' : "",
            'wit4_cputime-cpu0' : "",
            'wit4_cputime-cpu1' : "",
            'wit4_cputime-cpu2' : "",
            'wit4_cputime-cpu3' : "",
            'wit4_cputime-cpu4' : "",
            'wit4_cputime-cpu5' : "",
            'wit4_cputime-cpu6' : "",
            'wit4_cputime-cpu7' : "",
            'wit4_blkio-write' : "",
            'wit4_blkio-read' : "",
            'wit4_vcloud-newEnvironment' : "",
            'wit4_vcloud-additionalEnvironment' : "",
            'wit4_vcloud-outerwalltime' : "",
            'wit4_vcloud-memoryLimit' : "",
            'wit4_vcloud-memoryNodes' : "",
            'wit4_vcloud-memoryNodesAllocation' : "",
            'wit4_vcloud-cpuCores' : "",
            'wit4_vcloud-cpuCoresDetails' : "",
            'wit4_vcloud-debug' : "",
            'wit4_vcloud-maxLogFileSize' : "",

            
            # Hidden fields
            'category' : "",
            'exitcode' : "",
            'exitsignal' : "",
            'terminationreason' : "",
            'returnvalue' : "",
            
            # CPU
            'cputime-cpu0' : "",
            'cputime-cpu1' : "",
            'cputime-cpu2' : "",
            'cputime-cpu3' : "",
            'cputime-cpu4' : "",
            'cputime-cpu5' : "",
            'cputime-cpu6' : "",
            'cputime-cpu7' : "",
            
            'cpuenergy-pkg0' : "",
            'cpuenergy-pkg0-dram' : "",
            'cpuenergy-pkg0-uncore' : "",
            'cpuenergy-pkg0-core' : "",
            
            # IO
            'blkio-write' : "",
            'blkio-read' : "",
            
            # VCloud
            'vcloud-newEnvironment' : "",
            'vcloud-additionalEnvironment' : "",
            'vcloud-outerwalltime' : "",
            'vcloud-memoryLimit' : "",
            'vcloud-memoryNodes' : "",
            'vcloud-memoryNodesAllocation' : "",
            'vcloud-cpuCores' : "",
            'vcloud-cpuCoresDetails' : "",
            'vcloud-debug' : "",
            'vcloud-maxLogFileSize' : "",
        }
        
    def __len__(self):
        return len(self.__dictionary__)
    
    def __iter__(self):
        return iter(self.__dictionary__)
    
    def __delitem__(self, key):
        raise NotImplementedError
    
    def __setitem__(self, key, item):
        if key not in self.__dictionary__:
            raise KeyError("The key {} is not defined.".format(key))
        self.__dictionary__[key] = item
        
    def __getitem__(self, key):
        return self.__dictionary__[key]
    
    def __contains__(self, key):
        return key in self.__dictionary__
    
    def __str__(self, *args, **kwargs):
        output = "--- Run: ---\n" \
        + "Files: " + ", ".join(self.__dictionary__['files']) + "\n" \
        + "Name: " + self.__dictionary__['name'] + "\n" \
        + "Options: " + self.__dictionary__['options'] + "\n" \
        + "Properties: " + self.__dictionary__['properties'] + "\n" \
        + "Status: " + self.__dictionary__['status'] + "\n" \
        + "Log URL: " + str(self.getlogurl()) + "\n"
        return output
    
    def getlogurl(self):
        "Returns the URL for the log file of this particular run."
        
        if not self['name']:
            raise ValueError("Cannot get URL for log file as the field is empty")
        
        namesplit = self['name'].split("/")
        filename = namesplit[len(namesplit) - 1]
        return str(self.__logurlbase__ + filename + ".log")
    
    def getsanitizedname(self):
        "Returns the sanitized file name"
        if not self['name']:
            raise ValueError("Cannot sanitize empty file name")
        
        namesplit = self['name'].split("sv-benchmarks/c/")
        filename = namesplit[-1]
        return filename
        
    def hassameresult(self, other, ignoreCorrect):
        "Returns true if the other run has the same result as this or if the tool produced the correct result (if the flag is set)"
        
        if not isinstance(other, SVCOMPRun):
            raise Exception("The other object must be a run object. Type: " + str(type(other)))
        
        if self['name'] != other['name']:
            raise ValueError("Cannot compare results for different input files.")
        
        if self['status'] == other['status']:
            return True, other['status']
        
        if ignoreCorrect and self['status'] == "true" and (self['category'] == "correct" or self['category'] == "correct-unconfirmed"):
            return True, other['status']
        
        return (False, str(other['status']))
