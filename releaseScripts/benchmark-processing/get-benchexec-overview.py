#!/usr/bin/env python3

import argparse
import collections
import multiprocessing
import ntpath
import os
import re
import signal
import sys
import xml.etree.ElementTree as ET
from functools import reduce

from tqdm import tqdm

"""
(k,v) where
  k is the string we search,
  v iff the log line where we found the string is the one we want to show,
  !v iff the following log line is the one we want to show
"""
known_exceptions = {
    "UnsupportedOperationException: Unsupported type": True,
    "AssertionError: at least one of both input predicates is unknown": True,
    "command is only available in interactive mode": True,
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
    "SMTLIBException: Cannot handle literal (exists": True,
    "IllegalArgumentException: cannot bring into simultaneous update form": True,
    "No Boogie because C type is incomplete": True,
    "AssertionError: Invalid VarList": True,
    "AssertionError: Invalid Procedure": True,
    "AssertionError: No corresponding IProgramVar": True,
    "Wrong parameter type at index": True,
    "Undeclared identifier ": True,
    "Modifies not transitive": True,
    "encountered a call to a var args function and varargs usage is unknown": True,
    "UnsupportedOperationException: floating point operation not supported in non-bitprecise translation": True,
    "ClassCastException: de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer cannot be cast to de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive": True,
    "StackOverflowError: null": True,
    "No suitable toolchain file found": True,
    "No suitable file found in config dir": True,
    "AssertionError: var is still there": True,
    "IllegalStateException: Petrification does not provide enough thread instances": True,
    "IllegalStateException: ManagedScript already locked by": False,
    "ExceptionOrErrorResult": False,
    "was unable to instantiate class": True,
    "de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.ParserInitializationException: Parser initialization failed": True,
    "RESULT: Ultimate could not prove your program: Toolchain returned no result.": True,
}

UNEXPECTED_EXTERNAL_KILL = 'Killed from outside'

known_timeouts = {
    "Cannot interrupt operation gracefully because timeout expired. Forcing shutdown": True,
    "Toolchain execution was canceled (user or tool) before executing": True,
    "TimeoutResultAtElement": True,
    "TimeoutResult": True,
    "Killed by 15": True,
    UNEXPECTED_EXTERNAL_KILL: True,
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

known_wrapper_errors = {
    "Ultimate.py: error: argument --validate: File": True,
    "Checking for LTL property": True,
    "WARNING: YOUR LOGFILE WAS TOO LONG, SOME LINES IN THE MIDDLE WERE REMOVED.": True,
    "Skipped default analysis because property is memsafety": True,
}

str_no_result_unknown = "Unknown"
str_benchexec_timeout = "Timeout by benchexec"
str_benchexec_oom = "OOM by benchexec"

version_matcher = re.compile('^.*(\d+\.\d+\.\d+-\w+).*$')
order = [known_exceptions, known_timeouts, {str_benchexec_timeout: True, str_benchexec_oom: True}, known_unsafe,
         known_unknown, known_safe,
         known_wrapper_errors]
interesting_strings = reduce(lambda x, y: dict(x, **y), order)

enable_debug = False


def class_idx(result):
    if not result or not result[0]:
        return len(order) + 1
    return [i for i, e in enumerate(order) if result[0] in e][0]


class UnsupportedLogFile(ValueError):
    """
    Raised when the log file is not an Ultimate log file
    """
    pass


class Result:
    def __init__(self, result, call, version):
        self.version = version
        self.call = call
        self.result = result

    def __str__(self):
        return str(self.result)


def signal_handler(sig, frame):
    if sig == signal.SIGTERM:
        print('Killed by {}'.format(sig))
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
    debug('Looking at line {}'.format(line))

    for exc, v in interesting_strings.items():
        if exc in line:
            if v:
                new_result = exc, line
            else:
                new_result = exc, line_iter.__next__()
            debug('Found result {} with line {}'.format(exc, line))
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
    debug('Keeping old result because new one has lower priority')
    return result


def rescan_wrapper_preamble(file, call, version):
    '''
    If there was no result in the wrapper script log so far, we rescan it and search for errors reported directly by
    the wrapper script
    :param lines: Iterator over the lines
    :param call: A call if any was found
    :param version: A version if any was found
    :return:
    '''
    debug("Rescanning wrapper preamble")
    with open(file, 'rb') as f:
        # If the wrapper script was killed without any chance to print a message, the last elements are dots.
        # In this case we group the result as timeout and return a hardcoded line
        f.seek(-3, 2)
        last_elems = f.read()
        if b'...' == last_elems:
            return [Result((UNEXPECTED_EXTERNAL_KILL, '...'), call, version)]
        else:
            debug('Last 3 elements of file are {}'.format(last_elems))

    with open(file) as f:
        lines = [line.rstrip('\n') for line in f].__iter__()

        regex_file_does_not_exist = re.compile(".*File.*does not exist")
        result = None
        for line in lines:
            if not line:
                continue
            if 'Ultimate.py: error: argument' in line:
                debug("Found argument error")
                # hacky special case
                if '--validate' in line and regex_file_does_not_exist.match(line):
                    return [Result(scan_line(line, None, lines), None, None)]
                return [Result(None, None, None)]
            else:
                result = scan_line(line, result, lines)

        return [Result(result, call, version)]


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
    if not results:
        if result and default_call:
            # case where the bitvector run did not start, e.g., termination
            debug('Using default result: {}'.format(result))
            return [Result(result, default_call, version)]
        debug('No results for file {}'.format(file))
        return rescan_wrapper_preamble(file,
                                       default_call if default_call else (bitvec_call if bitvec_call else None),
                                       version)
    return results


def process_direct_call_log(file):
    result = None
    with open(file) as f:
        version = ''
        lines = [line.rstrip('\n') for line in f].__iter__()
        for line in lines:
            if not line:
                continue
            if "/java " in line or line.startswith("java"):
                call = line
                debug('Found Ultimate call {}'.format(call))
            elif line.startswith("This is Ultimate"):
                version = version_matcher.findall(line)[0]
                debug('Found Ultimate version {}'.format(version))
            else:
                result = scan_line(line, result, lines)
        if call is None:
            print(file + " has no call")
        return [Result(result, call, version)]


def process_log_file(file):
    with open(file) as f:
        lines = [line.rstrip('\n') for line in f]
        for line in lines:
            if 'Ultimate.py' in line:
                debug("Wrapper script detected")
                return process_wrapper_script_log(file)
            elif 'This is Ultimate' in line:
                debug("No wrapper script detected")
                return process_direct_call_log(file)
    raise UnsupportedLogFile('Encountered unrecognized file (not an Ultimate log file): {}'.format(file))


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
        if r.result[0] == str_no_result_unknown or not interesting_strings[r.result[0]]:
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


def __set_unknowns(results, file, timeout_ymls, oom_ymls):
    real_results = []
    for r in results:
        if r.result is None:
            basename = ntpath.basename(file)
            if any(f == basename for f in timeout_ymls):
                real_results += [Result((str_benchexec_timeout, '...'), r.call, r.version)]
            elif any(f == basename for f in oom_ymls):
                real_results += [Result((str_benchexec_oom, '...'), r.call, r.version)]
            else:
                real_results += [Result((str_no_result_unknown, file), r.call, r.version)]
        else:
            real_results += [r]
    return real_results


def __list_logfile_paths_in_dir(input_dir):
    for dirpath, dirnames, files in os.walk(input_dir):
        for file in files:
            if not file.endswith('.log'):
                continue
            yield os.path.join(dirpath, file)


def __list_xml_filepaths(input_dir):
    for xml in os.listdir(input_dir):
        file = os.path.join(input_dir, xml)
        if os.path.isfile(file) and file.endswith('.xml'):
            yield file


def consume_task(queue, results, timeout_ymls, oom_ymls):
    while True:
        path = queue.get()
        if path is None:
            break
        try:
            tmp_result = __set_unknowns(process_log_file(path), path, timeout_ymls, oom_ymls)
        except UnsupportedLogFile:
            continue
        results += tmp_result


def process_input_dir(input_dir, timeout_ymls, oom_ymls):
    results = multiprocessing.Manager().list()
    if os.path.isfile(input_dir):
        results += __set_unknowns(process_log_file(input_dir), input_dir, timeout_ymls, oom_ymls)
        log_file_count = 1
    else:
        local_cores = max(multiprocessing.cpu_count() - 4, 1)
        queue = multiprocessing.Queue(maxsize=local_cores)
        pool = multiprocessing.Pool(local_cores, initializer=consume_task,
                                    initargs=(queue, results, timeout_ymls, oom_ymls))

        progress_bar = tqdm([i for i in __list_logfile_paths_in_dir(input_dir)])
        log_file_count = len(progress_bar)

        for path in progress_bar:
            progress_bar.set_description('Processing ...{:100.100} [{:>3}C]'.format(path[len(input_dir):], local_cores))
            queue.put(path)

        # tell workers we're done
        for _ in range(local_cores):
            queue.put(None)
        pool.close()
        pool.join()
    return log_file_count, results


def __get_out_of_ressources_ymls(input_dir):
    xml_files = [f for f in __list_xml_filepaths(input_dir)]
    if len(xml_files) == 0:
        print('There are no benchexec .xml files in {}, cannot exclude timeouts properly'.format(input_dir))
        return []

    timeout_ymls = []
    oom_ymls = []
    for xml in __list_xml_filepaths(input_dir):
        root = ET.parse(xml).getroot()
        result = root.find(".")
        name = result.attrib["name"].split('.')
        toolname = name[0]
        for elem in root.findall(".//run"):
            # files = elem.attrib["files"]
            yml = elem.attrib["name"]
            base_yml = ntpath.basename(yml)
            status = elem.find("./column[@title='status']").attrib["value"]
            logfile_name = "{}.{}.log".format(toolname, base_yml)
            if status == "TIMEOUT":
                timeout_ymls += [logfile_name]
            elif status == "OUT OF MEMORY":
                oom_ymls += [logfile_name]
    return timeout_ymls, oom_ymls


def main():
    args = parse_args()
    input_dir = args.input[0]

    timeout_ymls, oom_ymls = __get_out_of_ressources_ymls(input_dir)
    log_file_count, results = process_input_dir(input_dir, timeout_ymls, oom_ymls)

    if log_file_count > len(results):
        print(
            'We processed {} .log files but collected only {} results, something is wrong!'.format(log_file_count,
                                                                                                   len(results)))
    else:
        print(
            'Overview of {} results from {} .log files ({} {}, {} {})'.format(len(results), log_file_count,
                                                                              len(timeout_ymls),
                                                                              str_benchexec_timeout, len(oom_ymls),
                                                                              str_benchexec_oom))
    print_results(results)


if __name__ == "__main__":
    if sys.platform == "linux" or sys.platform == "linux2":
        signal.signal(signal.SIGINT, signal_handler)
        signal.signal(signal.SIGTERM, signal_handler)
        # just ignore pipe exceptions
        signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    main()
