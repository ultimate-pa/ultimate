#!/usr/bin/python
"""
This is a simple python script that parses the somewhat cryptic output
of Matthias' test script and presents the information more concisely.

Written by Jan Leike 2014-06-26

In case anyone cares, this file is BSD-licensed.
"""

import sys
import os.path
import re


# Get the file name from $1
filename = sys.argv[1]
if not os.path.exists(filename):
	print "File not found: %s" % filename
	sys.exit(1)
# Get the output csv file name from $2 if there is a second argument
csv_filename = sys.argv[2] if len(sys.argv) >= 3 else '/tmp/ULTIMATE_output.csv'

# Read the whole file into memory
with open(filename, 'r') as f:
	data = f.read()
outputs = data.strip().split('\n\n')

# All the regular expressions
re_program = re.compile(r'(\S+\.c)')
re_toolchain = re.compile(r'(\S+\.xml)')
re_settings = re.compile(r'(\S+\.epf)')
re_time = re.compile(r'Automizer terminated after (\d+) and says')
#re_verdict = re.compile(r'(?: terminated after \d+ and says:\s+|!!!FAIL!!!\s*|!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!11[\w\W]*)(Termination|No\sResult|Nontermination|Exception|OutOfMemoryError|Timeout)')
re_verdict = re.compile(r'Test result:\s(\S+)')
all_res = (re_program, re_toolchain, re_settings, re_verdict) # re_time,
all_names = ('program', 'toolchain', 'settings', 'verdict') # 'time',
assert len(all_res) == len(all_names)

# Parse all the things!
results = []
for output in outputs:
	result = dict()
	for i in range(len(all_res)):
		re_ = all_res[i]
		name = all_names[i]
		match = re_.search(output)
		if match is not None:
			result[name] = match.group(1)
	# Make sure there is a verdict
	if not result.has_key('verdict'):
		result['verdict'] = 'Failed to parse ULTIMATE Output'
#		print output
	if len(result) > 0:
		results.append(result)

# Display some stats
print "%d results parsed" % len(results)
verdicts = set([result['verdict'] for result in results])
for verdict in verdicts:
	count = len(filter(lambda result: result['verdict'] == verdict, results))
	print '    %s: %d' % (verdict, count)

# Dump a csv file
if csv_filename != '':
	print 'Dumping a csv file to %s' % csv_filename
	with open(csv_filename, 'w') as f:
		f.write(','.join(all_names))
		for result in results:
			f.write('\n')
			f.write(','.join([result[n] if result.has_key(n) else '' 
			                  for n in all_names]))

