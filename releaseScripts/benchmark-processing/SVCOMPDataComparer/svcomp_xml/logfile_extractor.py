import logging
import re

import requests


class LogFileExtractor():
    "Extracts information from SVCOMP log files"
        
    def __init__(self, url):
        requests.logging.getLogger().setLevel(logging.ERROR)
        self.__url__ = url
        self.__response__ = requests.get(str(url))
        
    def getSettings(self):
        "Returns the used settings for the given URL"
        
        match = re.findall('\-tc.*(\/.*\.xml).*\-s.*(\/.*\.epf)', self.__response__.text, re.MULTILINE)

        if len(match) == 0:
            rematch = re.findall("No suitable toolchain file found.*$", self.__response__.text, re.MULTILINE)
            if len(rematch) > 0:
                return [ (str(rematch[0]), str(rematch[0])) ]
            raise IOError("No settings found in " + str(self.__url__))
        
        returnList = []
        
        for m in match:
            returnList.append((m[0].split("/")[-1], m[1].split("/")[-1]))
        
        if len(returnList) == 0:
            raise ValueError("Somehow, the split in the settings failed.")
        
        return returnList