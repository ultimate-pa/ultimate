#!/usr/bin/env python3

import xml.etree.ElementTree as ET
import os
import subprocess
import sys
import argparse
import signal
import re

def parse_args():
    argparser = argparse.ArgumentParser(description="Download and parse benchexec XML files and extract wrong results.")
    argparser.add_argument('-d','--directory', type=check_dir, nargs=1, metavar='<dir>', 
            help='The directory where we store .xml result files. The default is the current directory.',
            default=os.getcwd())
    argparser.add_argument('-p', '--printunsound', action='store_true', help='Print ' +
            'unsound files to corresponding result .xml file')
    argparser.add_argument('-v', '--verbose', action='store_true', help='Turn on verbose output.')
    argparser.add_argument('-f', '--file', type=check_file, nargs=1, metavar='<file>', 
            help='An input file where each line is an URL from which we can download an SVCOMP .xml file')
    argparser.add_argument('-o', '--output', type=str, nargs=1, metavar='<file>', 
            help='Write the unsound paths to a number of files with this prefix')

    args = argparser.parse_args()

    return args

def check_file(f):
    if not os.path.isfile(f):
        raise argparse.ArgumentTypeError("File %s does not exist" % f)
    return f

def check_dir(d):
    if not os.path.isdir(d):
        raise argparse.ArgumentTypeError("Directory %s does not exist" % d)
    return d

def merge_unsound(a, b):
    result = {**a, **b}
    for key, value in result.items():
        if key in a and key in b:
            result[key] = a[key].union(b[key])
    return result

def run_subprocess(command, error_msg, die=True):
    child = subprocess.Popen(command, stdout=subprocess.PIPE)
    stream = child.communicate()[0]
    if die and child.returncode != 0:
        print(error_msg)
        sys.exit(1)

def download_xml(folder, url):
    url = url.rstrip()
    if url:
        run_subprocess(['wget', '-t', '3', '-q', '--directory-prefix', folder, url], "Error downloading {}".format(url), True)

def extract_xml(file):
    run_subprocess(['bzip2', '-d', file], "Error extracting {} with bzip2".format(file),False)

def write_set_file(filename, unsounds):
    for key, value in unsounds.items():
        target_file = filename + '-' + re.sub(r"\s+", '_', key) + '.set'
        with open(target_file, 'w') as f:
            for elem in value:
                f.write("{}\n".format(elem))

def parse_xml(filename):
    tree = ET.parse(filename)
    root = tree.getroot()
    unsound = {}

    for run in root.findall('run'):
        for column in run.iter('column'):
            key = column.get('title')
            value = column.get('value')

            if key == "category" and value == "wrong":
                property = run.attrib['properties']
                unsound.setdefault(property, set()).add(run.get('name'))
    return unsound

def process_url_file(url_file, target_dir):
    with open(url_file) as fp:
        print("Downloading to folder {}".format(target_dir))
        for cnt, line in enumerate(fp):
            print("Downloading {}: {}".format(cnt, line).rstrip())
            download_xml(target_dir, line)

    for file in os.listdir(target_dir):
        if not file.endswith(".xml") and not file.endswith("urls"):
            absolute_path = os.path.join(target_dir, file)
            print("Extracting {}".format(absolute_path))
            extract_xml(absolute_path)


def main():
    args = parse_args()
    
    if args.file is not None: 
        process_url_file(args.file[0], args.directory[0])

    i=0
    unsounds = {}
    for file in os.listdir(args.directory[0]):
        if file.endswith(".xml"):
            absolute_path = os.path.join(args.directory[0], file)
            print("Parsing {}".format(absolute_path))
            unsound = parse_xml(absolute_path)
            if len(unsound) > 0:
                print("  Found {} unsound results".format(sum([len(v) for k,v in unsound.items()])))
                unsounds = merge_unsound(unsounds,unsound)
            i=i+1

    if i != 0:
        print("Unsound results:")
        for key, value in unsounds.items():
            for elem in value:
                print("{}: {}".format(key,elem))
    else:
        print("No .xml files in {}".format(args.directory))
    
    if args.output is not None and len(unsounds) > 0:
        print("Writing results to files with prefix {}".format(args.output[0]))
        write_set_file(args.output[0], unsounds)

def signal_handler(sig, frame):
    if sig == signal.SIGTERM:
        print('Killed by {}'.format(sig))
    print('Abort by user: you pressed Ctrl+C!')
    sys.exit(2)


if __name__ == "__main__":
    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)
    # just ignore pipe exceptions
    signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    main()
