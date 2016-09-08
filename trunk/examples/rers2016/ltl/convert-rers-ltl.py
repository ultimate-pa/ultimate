#!/usr/bin/env python2.7

from __future__ import print_function
import sys
import subprocess
import os
import fnmatch
import platform
import argparse
import string
import re 

def main():
    
    if ((len(sys.argv) != 2)):
        print ("Missing or too much arguments; specify just one file")
        sys.exit(0)
    
    symbolmap = dict(zip(string.ascii_uppercase, range(1, 27)))

    alltheregeexps = []
    for i, rpl in [('i', 'input'), ('o', 'output')]:
        for k, v in symbolmap.iteritems():
            alltheregeexps.append((re.compile(i + k), 'AP(' + rpl + '==' + str(v) + ')'))

    alltheregeexps.append((re.compile('\|'),'||'))
    alltheregeexps.append((re.compile('\&'),'&&'))

    with open(sys.argv[1]) as f:
        for line in f:
            if not line.startswith('#'):
                for (reg, rpl) in alltheregeexps:
                    line = reg.sub(rpl, line)
            sys.stdout.write(line)
            sys.stdout.flush()
   
    return


if __name__ == "__main__":
    main()
