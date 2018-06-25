#!/usr/bin/env python2.7

from __future__ import print_function

import argparse
import signal
import subprocess
import sys

import fnmatch
import os
import re
from stat import ST_MODE

version = 'DELTA-DEBUG'
ultimatedir = os.path.dirname(os.path.realpath(__file__))
configdir = os.path.join(ultimatedir, 'config')
datadir = os.path.join(ultimatedir, 'data')
enable_assertions = False


class _ExitCode:
    _exit_codes = ["SUCCESS", "FAIL_OPEN_SUBPROCESS", "FAIL_NO_INPUT_FILE", "FAIL_NO_WITNESS_TO_VALIDATE",
                   "FAIL_MULTIPLE_FILES", "FAIL_NO_TOOLCHAIN_FOUND", "FAIL_NO_SETTINGS_FILE_FOUND",
                   "FAIL_ULTIMATE_ERROR", "FAIL_NO_REDUCTION"]

    def __init__(self):
        pass

    def __getattr__(self, name):
        if name in _ExitCode._exit_codes:
            return _ExitCode._exit_codes.index(name)
        raise AttributeError("Exit code %s not found" % name)


ExitCode = _ExitCode()


def check_string_contains(strings, words):
    for string in strings:
        for word in words:
            if word == string:
                return True
    return False


def get_binary():
    ultimate_bin = [
        'java',
        '-Dosgi.configuration.area=' + os.path.join(datadir, 'config'),
        '-Xmx12G',
        '-Xms4m',
    ]

    if enable_assertions:
        ultimate_bin = ultimate_bin + ['-ea']

    ultimate_bin = ultimate_bin + [
        '-jar', os.path.join(ultimatedir, 'plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar'),
        '-data', datadir
    ]

    return ultimate_bin


def _init_child_process():
    new_umask = 0o022
    os.umask(new_umask)


def call_desperate(call_args):
    if call_args is None:
        call_args = []

    try:
        child_process = subprocess.Popen(call_args, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                         stderr=subprocess.STDOUT, shell=False, preexec_fn=_init_child_process)
    except:
        print('Error trying to open subprocess ' + str(call_args))
        sys.exit(ExitCode.FAIL_OPEN_SUBPROCESS)
    return child_process


def call_relaxed(call_args):
    if call_args is None:
        print('No call_args given')
        return '', None

    try:
        child_process = subprocess.Popen(call_args, stdout=subprocess.PIPE, preexec_fn=_init_child_process)
        return child_process.communicate()
    except Exception as ex:
        print('Error trying to start ' + str(call_args))
        print(str(ex))
        return '', None


def create_callargs(callargs, arguments):
    for arg in arguments:
        if isinstance(arg, list):
            for subarg in flatten(arg):
                callargs = callargs + [subarg]
        else:
            callargs = callargs + [arg]
    return callargs


def flatten(l):
    for el in l:
        if isinstance(el, list) and not isinstance(el, basestring) and not isinstance(el, (str, bytes)):
            for sub in flatten(el):
                yield sub
        else:
            yield el


def check_file(f):
    if not os.path.isfile(f):
        raise argparse.ArgumentTypeError("File %s does not exist" % f)
    return f


def check_dir(d):
    if not os.path.isdir(d):
        raise argparse.ArgumentTypeError("Directory %s does not exist" % d)
    return d


def debug_environment():
    # first, list all environment variables
    print('--- Environment variables ---')
    for env in os.environ:
        print(str(env) + '=' + str(os.environ.get(env)))

    print('--- Machine ---')
    call_relaxed_and_print(['uname', '-a'])
    call_relaxed_and_print(['cat', '/proc/cpuinfo'])
    call_relaxed_and_print(['cat', '/proc/meminfo'])

    print('--- Java ---')
    call_relaxed(['java', '-version'])

    print('--- Files ---')
    file_counter = 0
    dir_counter = 0
    for root, dirs, files in os.walk(ultimatedir):
        for a_dir in dirs:
            absdir = os.path.join(root, a_dir)
            rights = oct(os.stat(absdir)[ST_MODE])[-3:]
            print(str(rights) + ' D ' + str(absdir))
            dir_counter = dir_counter + 1
        for a_file in files:
            absfile = os.path.join(root, a_file)
            rights = oct(os.stat(absfile)[ST_MODE])[-3:]
            print(str(rights) + ' F ' + str(absfile))
            file_counter = file_counter + 1
    print(str(file_counter) + ' files total, ' + str(dir_counter) + ' dirs total')

    print('--- Versions ---')
    print(version)
    call_relaxed_and_print(create_callargs(get_binary(), ['--version']))

    print('--- umask ---')
    call_relaxed_and_print(['touch', 'testfile'])
    call_relaxed_and_print(['ls', '-al', 'testfile'])
    call_relaxed_and_print(['rm', 'testfile'])


def call_relaxed_and_print(call_args):
    stdout, stderr = call_relaxed(call_args)
    if stdout:
        print(stdout)
    if stderr:
        print('sdterr:')
        print(stderr)


def parse_args():
    # parse command line arguments
    global configdir
    global datadir
    global enable_assertions
    if (len(sys.argv) == 2) and (sys.argv[1] == '--version'):
        print(version)
        sys.exit(ExitCode.SUCCESS)

    if (len(sys.argv) == 2) and (sys.argv[1] == '--envdebug'):
        debug_environment()
        sys.exit(ExitCode.SUCCESS)

    parser = argparse.ArgumentParser(description='Ultimate wrapper script for SVCOMP')
    parser.add_argument('--version', action='store_true',
                        help='Print Ultimate.py\'s version and exit')
    parser.add_argument('--config', nargs=1, metavar='<dir>', type=check_dir,
                        help='Specify the directory in which the static config files are located; default is config/ '
                             'relative to the location of this script')
    parser.add_argument('--data', nargs=1, metavar='<dir>', type=check_dir,
                        help='Specify the directory in which the RCP config files are located; default is data/ '
                             'relative to the location of this script')
    parser.add_argument('-ea', '--enable-assertions', action='store_true',
                        help='Enable Java assertions')
    parser.add_argument('--full-output', action='store_true',
                        help='Print Ultimate\'s full output to stderr after verification ends')
    parser.add_argument('--envdebug', action='store_true',
                        help='Before doing anything, print as much information about the environment as possible')
    parser.add_argument('--file', metavar='<file>', nargs=1, type=check_file,
                        help='One C file')
    parser.add_argument('--output', metavar='<file>', nargs=1, help='File to which output is written')

    args, extras = parser.parse_known_args()

    if args.enable_assertions:
        enable_assertions = True

    if args.envdebug:
        debug_environment()

    if args.version:
        print(version)
        sys.exit(ExitCode.SUCCESS)

    if args.output:
        output = args.output
    else:
        output = "ultimate-output.log"

    if args.config:
        configdir = args.config[0]

    if args.data:
        print("Setting data dir to {0}".format(args.data[0]))
        datadir = args.data[0]

    return [args.file[0]], args.full_output, output, extras


def print_call_finished(name, process):
    if process.returncode == 0:
        print('\n' + name + ' finished normally')
    else:
        print('\n' + name + 'Ultimate finished with exit code ' + str(process.returncode))


def start_processes(list_of_calls):
    rtr = []
    for call in list_of_calls:
        call_proc = call_desperate(call)
        rtr += [call_proc]
        print('Creating process {} by calling {}'.format(call_proc.procid(), call))
    return rtr


def poll_processes(list_of_processes, is_interesting, is_interesting_initial, write_output):
    # poll the output

    reductions = dict()
    for fun, default in zip(is_interesting, is_interesting_initial):
        reductions[fun] = default

    while True:
        lines = []
        for process in list_of_processes:
            lines += [process.stdout.readline().decode('utf-8', 'ignore')]
            process.poll()

        is_running = False
        for process, line in zip(list_of_processes, lines):
            is_running = is_running or (process.returncode is not None and not line)
            if is_running:
                break

        if not is_running:
            for process in list_of_processes:
                print_call_finished(process.procid(), process)
            break

        if write_output:
            for process, line in zip(list_of_processes, lines):
                if not line:
                    continue
                print('[{}] {}'.format(process.procid(), line))

        for line, fun in zip(lines, is_interesting):
            if line:
                reductions[fun] = fun(reductions[fun], line)

        if all(reductions.values()):
            print('Successful reduction')
            sys.exit(ExitCode.SUCCESS)

    print('No reduction')
    sys.exit(ExitCode.FAIL_NO_REDUCTION)


def delta_debug_smtinterpol(input_files, verbose, output, extras):
    # execute ultimate and assume that -tc and -s are given in extras
    ultimate_bin = get_binary()
    input = extras[-1]
    extras = extras[:-1]
    ultimate_call = create_callargs(ultimate_bin, extras + ['-i', input_files])
    z3_call = ['z3', 'fixedpoint.engine=spacer', input]

    z3_interesting = lambda acc, line: acc or line.startswith('sat')
    ult_interesting = lambda acc, line: acc or line.find('CounterExampleResult') != -1

    processes = start_processes([ultimate_call, z3_call])
    poll_processes(processes, [ult_interesting, z3_interesting], [False, False], verbose)

    sys.exit(ExitCode.FAIL_NO_REDUCTION)


def delta_debug_creduce(input_files, verbose, output, extras):
    # execute ultimate and assume that -tc and -s are given in extras
    ultimate_bin = get_binary()
    input = extras[-1]
    extras = extras[:-1]
    ultimate_call = create_callargs(ultimate_bin, extras + ['-i', input_files])
    gcc_call = ['gcc', '-std=c11', '-pedantic', '-w', '-fsyntax-only', input]

    ult_interesting = lambda acc, line: acc or x.find('CounterExampleResult') != -1
    # any gcc output says that there is a syntax error
    gcc_interesting = lambda acc, line: False

    processes = start_processes([ultimate_call, gcc_call])
    poll_processes(processes, [ult_interesting, gcc_interesting], [False, True], verbose)

    sys.exit(ExitCode.FAIL_NO_REDUCTION)


def main():
    input_files, verbose, output, extras = parse_args()

    output_file = open(output, 'a')
    sys.stdout = output_file
    sys.stderr = output_file
    delta_debug_smtinterpol(input_files, verbose, output, extras)
    # delta_debug_creduce(input_files, verbose, output, extras)


if __name__ == "__main__":
    sys.exit(ExitCode.FAIL_NO_REDUCTION)
