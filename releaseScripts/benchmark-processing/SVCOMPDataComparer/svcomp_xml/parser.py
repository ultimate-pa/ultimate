from datetime import datetime
import os
import re

from svcomp_xml.result import SVCOMPResult
from svcomp_xml.run import SVCOMPRun
import xml.etree.ElementTree as ET


class SVCOMPParser(object):
    
    def __init__(self, year):
        "Constructor for SVCPMPParser that takes the year of the SV-COMP results, e.g. 2017"
        self.__year__ = year
        self.__urlbase__ = "https://sv-comp.sosy-lab.org/" + str(self.__year__) + "/results/results-verified/"

    def parsexml(self, filename):
        "Parses a result file from SVCOMP"
        tree = ET.parse(filename)
        root = tree.getroot()
        suffix = ".".join(os.path.basename(filename).split(".")[:2])
        logurlbase = self.__urlbase__ + suffix + '.logfiles/sv-comp' + str(self.__year__)[2:] + '.'
        
        returnResult = SVCOMPResult()
        returnResult.benchmarkname = root.get('benchmarkname')
        returnResult.block = root.get('block')
        returnResult.cpuCores = root.get('cpuCores')
        startdate, enddates = self.__parsedate__(root.get('date'))
        returnResult.dateStart = startdate
        returnResult.dateEnd = enddates
        
        for run in root.findall('run'):
            parsedRun = self.__parserun__(run, logurlbase)
            returnResult.__runs__.append(parsedRun)
            
        return returnResult

    def __parsedate__(self, datestring):
        dateregex = r"\d\d\d\d-\d\d-\d\d \d\d\:\d\d\:\d\d \w+"
        dateformat = "%Y-%m-%d %H:%M:%S %Z"
        
        startdate = re.match(r"^(" + dateregex + ").*?\[\[.*?$", datestring)
        enddates = re.findall(r"\[\[ (.+?) \]\]", datestring)
                
        if startdate is None:
            # Possibly no end dates given. Trying to parse for single date.
            startdatesingle = re.match(r"^(" + dateregex + ").*?$", datestring)
            if startdatesingle is None:
                # Can't do anything else... Date unknown.
                raise Exception("Cannot identify date for string: " + datestring)

            startd = startdatesingle.group(1)            
            hasEnd = False
        else:
            startd = startdate.group(1)
            hasEnd = True
            
        
        sdate = datetime.strptime(startd, dateformat)
        
        edates = []
        
        if not hasEnd:
            return sdate, edates
        
        for dat in enddates:
            currentdate = re.match(r"(" + dateregex + ")", dat)
            parseddate = datetime.strptime(currentdate.group(1), dateformat)
            edates.append(parseddate)
            
        return sdate, edates

    def __parserun__(self, run, logurlbase):
        "Parses the run information"
        returnRun = SVCOMPRun(logurlbase)
        
        returnRun['files'] = run.get('files').strip("[").strip("]").split(",")
        returnRun['name'] = run.get('name')
        returnRun['options'] = run.get('options')
        returnRun['properties'] = run.get('properties')
        
        self.__parsecolumns__(run, returnRun)
        
        return returnRun
    
    def __parsecolumns__(self, run, returnRun):
        "Parses the columns in a given run"
        
        for column in run.iter('column'):
            key = column.get('title')
            value = column.get('value')
            
            returnRun[key] = value
