# Prints either to stdout or to a file
import sys

class Outputter(object):
    
    def __init__(self, toFile, fileName):
        "Initialized the outputter"
        self.__toFile__ = toFile
        
        if self.__toFile__:
            self.__file__ = open(str(fileName), 'w')
    
    def write(self, text):
        "Prints text without a new line"
        
        sys.stdout.write(str(text))
        sys.stdout.flush()
        
        if self.__toFile__:
            self.__file__.write(str(text))
            self.__file__.flush()
        
    def writeLine(self, text):
        "Prints text and ends with a new line"
        
        sys.stdout.write(str(text) + "\n")
        sys.stdout.flush()
        
        if self.__toFile__:
            self.__file__.write(str(text) + "\n")
            self.__file__.flush()
            
    def close(self):
        if self.__toFile__:
            self.__file__.close()