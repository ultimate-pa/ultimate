#!/usr/bin/env python3

import argparse
import re
import sys


def get_top_operands(s):
    operands = []
    pstack = []
    last_space = None

    for i, c in enumerate(s):
        if c == '(':
            pstack.append(i)
        elif c == ')':
            if len(pstack) == 0:
                print(s)
                raise IndexError("No matching closing parens at: " + str(i))
            j = pstack.pop()
            last_space = None 
            if len(pstack) == 0:
                operands.append(s[j:i + 1])
        elif c == ' ':
            if not last_space:
                last_space = i
            else:
                if len(pstack) == 0:
                    # we have a top level operand without parenthesis
                    operands.append(s[last_space:i + 1])
                last_space = i

    if len(pstack) > 0:
        print(s)
        raise IndexError("No matching opening parens at: " + str(pstack.pop()))
    return operands


def split_and(s):
    if s.startswith('(and'):
        rtr = []
        for operand in get_top_operands(s[5:len(s) - 1]):
            rtr = rtr + split_and(operand)
        return rtr
    else:
        return [s]


parser = argparse.ArgumentParser(description='Convert (assert (and o1 o2 ...)) to (assert o1) (assert o2) (assert ...)')
parser.add_argument('-i', '--input', nargs=1, metavar='<file>', required=True, help='Specify input file')
parser.add_argument('-o', '--output', nargs=1, metavar='<file>', required=True, help='Specify output file')

try:
    args, extras = parser.parse_known_args()
except argparse.ArgumentError as exc:
    print(exc.message + '\n' + exc.argument)
    sys.exit(1)

input_script = args.input[0]
output_script = args.output[0]
if input_script == output_script:
    print('Input and output file must be different')
    sys.exit(1)

try:
    with open(input_script, encoding='utf-8') as f, open(output_script, 'w', encoding='utf-8') as o:
        for line in f.readlines():
            if line.startswith("(assert (!"):
                m = re.search('\(assert \(! (.*?) :named (.*?)\)\)', line)
                formula = m.group(1)
                if formula == 'true':
                    continue
                name = m.group(2)
                asserts = split_and(formula)
                if len(asserts) == 1:
                    o.write('(assert (! {} :named {}))\n'.format(asserts[0], name))
                else:
                    i = 0
                    for sub in asserts:
                        o.write('(assert (! {} :named {}))\n'.format(sub, name + '_' + str(i)))
                        i = i + 1
            else:
                o.write(line)
except FileNotFoundError as exc: 
    print('Did not find ' + input_script)
    print('Arguments were '+ str(args))
    sys.exit(1)