#!/usr/bin/env python3

import argparse
import collections
import os
import re
import signal
import sys
from functools import reduce

"""
(k,v) where k = the string we search, v iff this line is important, !v iff we should use the next 
"""
known_exceptions = {
    "Argument of \"settings\" has invalid value": True,
    "encountered a call to a var args function, var args are not supported at the moment": True,
    "we do not support pthread": True,
    "unable to decide satisfiability of path constraint": True,
    "overapproximation of large string literal": True,
    "TerminationAnalysisResult: Unable to decide termination": True,
    "An exception occured during the execution of Ultimate: The toolchain threw an exception": True,
    "overapproximation of shiftRight": True,
    "overapproximation of overflow check for bitwise shift operation": True,
    "overapproximation of bitwiseAnd": True,
    "overapproximation of shiftLeft": True,
    "overapproximation of memtrack": True,
    "There is insufficient memory for the Java Runtime Environment to continue": True,
    "UnsupportedSyntaxResult": False,
    "TypeErrorResult": False,
    "SyntaxErrorResult": False,
    "TypeCheckException": True,
    "ExceptionOrErrorResult": False,
    "RESULT: Ultimate could not prove your program: Toolchain returned no result.": True,
}

known_timeouts = {
    "Cannot interrupt operation gracefully because timeout expired. Forcing shutdown": True,
    "Toolchain execution was canceled (user or tool) before executing": True,
    "TimeoutResultAtElement": True,
    "TimeoutResult": True,
}

known_safe = {
    "AllSpecificationsHoldResult": True,
    "TerminationAnalysisResult: Termination proven": True,
}

known_unsafe = {
    "CounterExampleResult": True,
    "NonterminatingLassoResult": True,
}

known_unknown = {
    "UnprovableResult": True,
}

version_matcher = re.compile('^.*(\d+\.\d+\.\d+-\w+).*$')
order = [known_exceptions, known_timeouts, known_unsafe, known_unknown, known_safe]
interesting_strings = reduce(lambda x, y: dict(x, **y), order)

enable_debug = False


def class_idx(result):
    if not result or not result[0]:
        return len(order) + 1
    return [i for i, e in enumerate(order) if result[0] in e][0]


class Result:
    def __init__(self, result, call, version):
        self.version = version
        self.call = call
        self.result = result

    def __str__(self):
        return str(self.result)


def signal_handler(sig, frame):
    print('Abort by user: you pressed Ctrl+C!')
    sys.exit(2)


def limit(msg, lim):
    if lim < 4:
        raise ValueError('limit must be larger or equal 4 but was {}'.format(lim))
    if len(msg) > lim:
        return msg[0:lim - 3] + '...'
    return msg.ljust(lim, ' ')


def debug(msg):
    if enable_debug:
        print(msg)


def parse_args():
    try:
        parser = argparse.ArgumentParser(description='Scan Ultimate log file for exception results')
        parser.add_argument('-i', '--input', nargs=1, metavar='<dir>', required=True,
                            help='Specify directory containing Ultimate log files or single log file')
        args = parser.parse_args()
        if not os.path.isdir(args.input[0]) and not os.path.isfile(args.input[0]):
            print('Input does not exist')
            sys.exit(1)
        return args
    except argparse.ArgumentError as exc:
        print(exc.message + '\n' + exc.argument)
        sys.exit(1)


def scan_line(line, result, line_iter):
    new_result = None

    for exc, v in interesting_strings.items():
        if exc in line:
            if v:
                new_result = exc, line
            else:
                new_result = exc, line_iter.__next__()
            break

    if not result and new_result:
        return new_result
    if result and not new_result:
        return result
    if not result and not new_result:
        return result

    new_class = class_idx(new_result)
    old_class = class_idx(result)
    if new_class < old_class:
        return new_result
    return result


def process_wrapper_script_log(file):
    results = []
    default = True
    wrapper_preamble = True
    collect_call = False
    version = None
    result = None
    default_call = None
    bitvec_call = None
    with open(file) as f:
        lines = [line.rstrip('\n') for line in f].__iter__()
        for line in lines:
            if not line:
                continue
            if wrapper_preamble:
                if "Using bit-precise analysis" in line:
                    default = False
                elif line.startswith("Calling Ultimate with:"):
                    call = [line]
                    collect_call = True
                elif collect_call:
                    if 'Execution finished normally' in line:
                        collect_call = False
                        if default:
                            default_call = call[:-1]
                            debug('Found default call {}'.format(default_call))
                        else:
                            bitvec_call = call[:-1]
                            debug('Found bitvector call {}'.format(bitvec_call))
                    else:
                        call += [line]
                elif '--- Real Ultimate output ---' in line:
                    wrapper_preamble = False
            else:
                if line.startswith("This is Ultimate"):
                    new_version = version_matcher.findall(line)[0]
                    if version and not new_version == version:
                        raise ValueError(
                            'Found different Ultimate versions in one log file. First was {} and second was {}'.format(
                                version, new_version))
                    version = new_version
                    debug('Found Ultimate version {}'.format(version))
                elif "### Bit-precise run ###" in line:
                    debug('Found default result: {}'.format(result))
                    results += [Result(result, default_call, version)]
                    result = None
                else:
                    result = scan_line(line, result, lines)
        if bitvec_call:
            debug('Found bitvec result: {}'.format(result))
            results += [Result(result, bitvec_call, version)]
        return results


def process_direct_call_log(file):
    result = None
    with open(file) as f:
        lines = [line.rstrip('\n') for line in f].__iter__()
        for line in lines:
            if not line:
                continue
            if line.startswith("java"):
                call = line
                debug('Found Ultimate call {}'.format(call))
            elif line.startswith("This is Ultimate"):
                version = version_matcher.findall(line)[0]
                debug('Found Ultimate version {}'.format(version))
            else:
                result = scan_line(line, result, lines)
        return [Result(result, call, version)]


def process_log_file(file):
    with open(file) as f:
        lines = [line.rstrip('\n') for line in f]
        for line in lines:
            if './Ultimate.py' in line:
                return process_wrapper_script_log(file)
            elif 'This is Ultimate' in line:
                return process_direct_call_log(file)
        return []


def print_results(results):
    cnt = collections.Counter()
    for r in results:
        cnt[r.result[0]] += 1

    print('Categories')
    for cat, i in cnt.most_common():
        print('{:>7}  {}'.format(i, cat))
    print()

    print('Actual results')
    inner_counter = collections.Counter()
    processed = {}
    for r in results:
        if r.result[0] == 'Unknown' or not interesting_strings[r.result[0]]:
            key = r.result[1]
        else:
            key = r.result[0]
        inner_counter[key] += 1
        processed[key] = r

    resort = []
    for subcat, j in inner_counter.most_common():
        r = processed[subcat].result
        msg = '{:>7}  {}  {}:'.format(j, limit(r[0], 20), r[1])
        if j < 10:
            resort += [msg]
        else:
            print(msg)

    for msg in sorted(resort, reverse=True):
        print(msg)


def set_unknowns(results, file):
    return list(
        map(lambda x: Result(("Unknown", file), x.call, x.version) if x.result is None else x, results))


def main():
    args = parse_args()
    input = args.input[0]

    results = []
    if os.path.isfile(input):
        results += set_unknowns(process_log_file(input), input)
    else:
        for dirpath, dirnames, files in os.walk(input):
            for file in files:
                if not file.endswith('.log'):
                    continue
                path = os.path.join(dirpath, file)
                debug('Processing {}'.format(path))
                results += set_unknowns(process_log_file(path), path)

    print_results(results)


if __name__ == "__main__":
    signal.signal(signal.SIGINT, signal_handler)
    # just ignore pipe exceptions
    signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    main()
