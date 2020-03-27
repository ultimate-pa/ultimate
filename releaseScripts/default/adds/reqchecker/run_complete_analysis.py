#!/usr/bin/env python3

import argparse
import logging
import os
import pathlib
import platform
import re
import shutil
import signal
import subprocess
import sys
from typing import Optional, List

from tqdm import tqdm


class _ExitCode:
    """
    Specify a named exit code for global usage.
    """
    _exit_codes = ["SUCCESS", "FAIL_NO_ACTION", "FAIL_SIGNAL", "FAIL_FILE_AS_DIR", "FAIL_SUBPROCESS",
                   "FAIL_MISSING_LOGFILE", "USER_DO_NOT_CREATE_DIR", "USER_DO_NOT_DELETE_DIR",
                   "USER_DO_NOT_DELETE_FILE"]

    def __init__(self):
        pass

    def __getattr__(self, name):
        if name in _ExitCode._exit_codes:
            return _ExitCode._exit_codes.index(name)
        raise AttributeError("Exit code %s not found" % name)


class SimpleMatcher:
    def __init__(self, regex):
        self.__regex = re.compile(regex)
        self.__match = None

    def match(self, line):
        self.__match = self.__regex.match(line)
        return bool(self.__match)

    def group(self, i):
        return self.__match.group(i)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="This script is a wrapper script for Ultimate ReqAnalyzer. "
                    "It shows progress and handles the execution of test generation and requirement analysis."

    )

    parser.add_argument("input", metavar='<file>', type=check_file,
                        help='Requirement file. (*.req)'
                        )

    parser.add_argument("--log", metavar="<file>", nargs=1, default=None,
                        help="Log the output of the script to <file>")
    parser.add_argument("--log-level", dest="log_level", nargs='?', default=logging.INFO,
                        choices=["DEBUG", "INFO", "ERROR", "WARN"],
                        help="Log level of the script. Default: INFO")
    parser.add_argument("-f", "--force", action="store_true", help="Suppress all prompts")

    parser.add_argument("-o", "--output", metavar='<dir>', type=str, default=None,
                        help='Folder where reports (*.relevant.log, vacuous .req subsets, etc.) are saved. '
                             'Default: Beside input file.'
                        )

    parser.add_argument("--tmp-dir", metavar='<dir>', type=str, default=None,
                        help='Folder where full Ultimate logs and .smt2 dumps are saved. '
                             'Default: In reqcheck/ besides input file.'
                        )

    parser.add_argument("-ar", "--analyze-requirements", action="store_true",
                        help="Run requirement analysis.")
    parser.add_argument("-gt", "--generate-tests", action="store_true",
                        help="Run test generation.")

    parser.add_argument('--rt-inconsistency-range', type=int, default=2,
                        help='The amount of requirements which are checked together for RT-inconsistency. Default: 2')
    parser.add_argument('--timeout-per-assertion', type=int, default=900,
                        help='Amount of seconds until analysis of an assertion is timed out. Default: 900')

    config_files = parser.add_argument_group(title='Ultimate location and configuration files',
                                             description='Control the location of Ultimate ReqChecker itself and'
                                                         ' various config files. '
                                                         'You should normally never change these settings. '
                                             )
    config_files.add_argument('--ultimate-dir', type=check_dir, metavar='<file>', default='.',
                              help="The path to Ultimate ReqAnalyzer."
                                   "Default: ."
                              )

    config_files.add_argument('--reqcheck-toolchain', type=check_file, metavar='<file>', default='config/ReqCheck.xml',
                              help="The Ultimate toolchain file (.xml) that will be used during requirements checking."
                                   "Default: config/ReqCheck.xml"
                              )

    config_files.add_argument('--reqcheck-settings', type=check_file, metavar='<file>',
                              default='config/ReqCheck-nonlin.epf',
                              help="The Ultimate settings file (.epf) that will be used during requirements checking."
                                   "Default: config/ReqCheck-nonlin.epf"
                              )

    config_files.add_argument('--testgen-toolchain', type=check_file, metavar='<file>', default='config/ReqToTest.xml',
                              help="The Ultimate toolchain file (.xml) that will be used during test generation."
                                   "Default: config/ReqToTest.xml"
                              )

    config_files.add_argument('--testgen-settings', type=check_file, metavar='<file>',
                              default='config/ReqCheck-ReqToTest.epf',
                              help="The Ultimate settings file (.epf) that will be used during test generation."
                                   "Default: config/ReqCheck-ReqToTest.epf"
                              )

    args = parser.parse_args()

    if not args.analyze_requirements and not args.generate_tests:
        parser.print_help()
        sys.exit(ExitCode.FAIL_NO_ACTION)

    return args


def token_string_or_file(arg):
    if not os.path.exists(arg):
        return arg
    else:
        return open(arg, "r").read().strip()


def check_dir(arg):
    if not os.path.exists(arg):
        msg = "Directory {} does not exist".format(arg)
        print(msg)
        raise argparse.ArgumentError(msg)
    return arg


def check_file(arg):
    if not os.path.isfile(arg):
        msg = "{} does not exist or is not a file".format(arg)
        print(msg)
        raise argparse.ArgumentError(msg)
    return arg


def create_dirs_if_necessary(args, dirs):
    for d in dirs:
        if os.path.isdir(d):
            continue

        if not confirm_if_necessary(args, '{} does not exist, should I create it?'.format(d)):
            sys.exit(ExitCode.USER_DO_NOT_CREATE_DIR)

        os.makedirs(d)


def delete_dir_if_necessary(args, d):
    if os.path.isfile(d):
        logging.fatal("Will not delete file {}".format(d))
        sys.exit(ExitCode.FAIL_FILE_AS_DIR)

    if not os.path.isdir(d):
        return

    if not confirm_if_necessary(args, '{} exists, should I delete it?'.format(d)):
        sys.exit(ExitCode.USER_DO_NOT_DELETE_DIR)

    shutil.rmtree(d)


def delete_file_if_necessary(args, file):
    if not os.path.isfile(file):
        return

    if not confirm_if_necessary(args, '{} exists, should I delete it?'.format(file)):
        sys.exit(ExitCode.USER_DO_NOT_DELETE_FILE)

    os.remove(file)


def init_child_process():
    new_umask = 0o022
    os.umask(new_umask)


def call_desperate(call_args: Optional[List[str]]):
    if call_args is None:
        call_args = []

    try:
        if platform == "linux" or platform == "linux2":
            child_process = subprocess.Popen(call_args, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                             stderr=subprocess.STDOUT, shell=False,
                                             preexec_fn=init_child_process)
        else:
            child_process = subprocess.Popen(call_args, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                             stderr=subprocess.STDOUT, shell=False)
    except Exception as ex:
        logger.fatal('Error trying to open subprocess {}'.format(str(call_args)))
        logger.fatal(ex)
        sys.exit(ExitCode.FAIL_SUBPROCESS)
    return child_process


def confirm(prompt=None, default_response=False) -> bool:
    """prompts for yes or no response from the user. Returns True for yes and
    False for no.

    'resp' should be set to the default value assumed by the caller when
    user simply types ENTER.

    >>> confirm(prompt='Create Directory?', default_response=True)
    Create Directory? [y]|n:
    True
    >>> confirm(prompt='Create Directory?', default_response=False)
    Create Directory? [n]|y:
    False
    >>> confirm(prompt='Create Directory?', default_response=False)
    Create Directory? [n]|y: y
    True
    """

    if prompt is None:
        prompt = 'Confirm'
    if default_response:
        prompt = '%s [%s]|%s: ' % (prompt, 'y', 'n')
    else:
        prompt = '%s [%s]|%s: ' % (prompt, 'n', 'y')

    while True:
        ans = input(prompt)
        if not ans:
            return default_response
        if ans not in ['y', 'Y', 'n', 'N']:
            print('please enter y or n.')
            continue
        if ans == 'y' or ans == 'Y':
            return True
        if ans == 'n' or ans == 'N':
            return False


def confirm_if_necessary(args, prompt: str = None, default_response: bool = False):
    if args.force:
        return True
    return confirm(prompt, default_response)


def signal_handler(sig, frame):
    print('Killed by {}'.format(sig))
    sys.exit(ExitCode.FAIL_SIGNAL)


def update_line(ultimate_process, logfile):
    line = ultimate_process.stdout.readline().decode('utf-8', 'ignore')

    ultimate_process.poll()
    if ultimate_process.returncode is not None and not line:
        if ultimate_process.returncode == 0:
            logger.info('Execution finished normally')
        else:
            logger.error('Execution finished with exit code {}'.format(str(ultimate_process.returncode)))
        return None, True
    logfile.write(line)
    return line, False


def update_progress_bar_plugin_end(line, progress_bar):
    if progress_bar and re_plugin_end.match(line):
        progress_bar.close()
        progress_bar = None
    return progress_bar


def create_and_update_progress_bar_phase1(line, counter, total, progress_bar):
    if re_phase1_start.match(line):
        total = int(re_phase1_start.group(1))
        progress_bar = tqdm(total=total)
        progress_bar.set_description('Phase 1: Creating rt-inconsistency checks')
    elif re_phase1_progress.match(line):
        progress = int(re_phase1_progress.group(1))
        counter += progress
        progress_bar.update(progress)
    elif re_phase1_end.match(line):
        progress = int(re_phase1_end.group(1))
        if progress == total:
            progress_bar.update(total - counter)
            counter = total
    else:
        progress_bar = update_progress_bar_plugin_end(line, progress_bar)
    return counter, total, progress_bar


def create_and_update_progress_bar_phase2(line, counter, total, progress_bar, desc):
    if re_phase2_start.match(line):
        total = int(re_phase2_start.group(1))
        progress_bar = tqdm(total=total)
        progress_bar.set_description(desc)
    elif re_phase2_description.match(line):
        progress_bar.set_description(
            '{} {} for requirement {}'.format(desc, re_phase2_description.group(1), re_phase2_description.group(2))
        )
    elif re_phase2_progress.match(line):
        progress = int(re_phase2_progress.group(3))
        counter += progress
        progress_bar.update(1)
    else:
        progress_bar = update_progress_bar_plugin_end(line, progress_bar)
    return counter, total, progress_bar


def handle_log(args):
    global logger
    handler = logging.FileHandler(args.log)
    handler.setLevel(args.log_level)
    log_formatter = logging.Formatter('%(asctime)s %(name)-8s %(levelname)-6s: %(message)s')
    handler.setFormatter(log_formatter)
    logger.addHandler(handler)


def handle_analyze_requirements(args):
    logger.info('Running ReqChecker')

    os.chdir(args.ultimate_dir)
    dump_folder = os.path.join(args.tmp_dir, 'dump', args.req_basename)
    delete_dir_if_necessary(args, dump_folder)
    logger.info('Creating dump folder {}'.format(dump_folder))
    pathlib.Path(dump_folder).mkdir(parents=True, exist_ok=True)
    delete_file_if_necessary(args, args.reqcheck_log)

    logger.info('Analyzing {}'.format(args.input))
    logger.info('Using logfile {}'.format(args.reqcheck_log))

    cmd = [
        'java',
        '-Dosgi.configuration.area=config/',
        '-Xmx100G',
        '-Xss4m',
        '-jar', 'plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar',
        '-tc', args.reqcheck_toolchain,
        '-s', args.reqcheck_settings,
        '-i', args.input,
        '--core.print.statistic.results', 'false',
        '--traceabstraction.dump.smt.script.to.file', 'true',
        '--traceabstraction.to.the.following.directory', dump_folder,
        '--traceabstraction.limit.analysis.time', str(args.timeout_per_assertion),
        '--pea2boogie.always.use.all.invariants.during.rt-inconsistency.checks', 'true',
        '--pea2boogie.check.vacuity', 'true',
        '--pea2boogie.check.consistency', 'true',
        '--pea2boogie.check.rt-inconsistency', 'true',
        '--pea2boogie.report.trivial.rt-consistency', 'false',
        '--pea2boogie.rt-inconsistency.range', str(args.rt_inconsistency_range),
    ]

    ultimate_process = call_desperate(cmd)

    relevant_log = []

    progress_bar = None

    phase1_counter = 0
    phase1_total = 0
    phase2_counter = 0
    phase2_total = 0
    logger.info('Started ReqChecker with PID {}'.format(ultimate_process.pid))
    with open(args.reqcheck_log, 'w', buffering=1) as logfile:
        line = ""
        while True:
            last_line = line
            line, end_reached = update_line(ultimate_process, logfile)
            if end_reached:
                break

            if "ReqCheckSuccessResult" in last_line or "ReqCheckFailResult" in last_line:
                relevant_log += [last_line + line]

            # show and update progress bars
            phase1_counter, phase1_total, progress_bar = create_and_update_progress_bar_phase1(
                line, phase1_counter, phase1_total, progress_bar
            )
            phase2_counter, phase2_total, progress_bar = create_and_update_progress_bar_phase2(
                line, phase2_counter, phase2_total, progress_bar, "Phase 2: Checking assertion(s)"
            )

    logger.info('Extracting results to {}'.format(args.reqcheck_relevant_log))
    with open(args.reqcheck_relevant_log, 'w+') as relevant_logfile:
        relevant_logfile.write(os.linesep.join(relevant_log))

    # Postprocess results with vacuity extractor.
    # Note the spaces
    is_vacuous = any(' vacuous ' in l for l in relevant_log)

    # TODO: Call vac_extractor python
    if is_vacuous:
        logger.info('Analyzing reasons for vacuity')
        # TODO: Integrate extract_vac_reasons.sh
        # shutil.move('*.vac.req', args.log_folder)
        logger.warning("NO VACUITY EXTRACTION YET")
    else:
        logger.info('No vacuities found.')


def handle_generate_tests(args):
    logger.info('Running test generation')
    logger.info('Using logfile {}'.format(args.testgen_log))

    cmd = [
        'java',
        '-Dosgi.configuration.area=config/',
        '-Xmx100G',
        '-Xss4m',
        '-jar', 'plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar',
        '-tc', args.testgen_toolchain,
        '-s', args.testgen_settings,
        '-i', args.input,
        '--core.print.statistic.results', 'false',
        '--traceabstraction.limit.analysis.time', str(args.timeout_per_assertion),
        '--rcfgbuilder.simplify.code.blocks', 'false',
        '--rcfgbuilder.size.of.a.code.block', 'LoopFreeBlock',
        '--rcfgbuilder.add.additional.assume.for.each.assert', 'false',
    ]

    ultimate_process = call_desperate(cmd)

    is_relevant = False
    counter = 0
    total = 0
    progress_bar = None
    logger.info('Started ReqChecker with PID {}'.format(ultimate_process.pid))
    with open(args.testgen_log, 'w') as logfile, open(args.testgen_relevant_log, 'w') as relevant_logfile:
        while (True):
            line, end_reached = update_line(ultimate_process, logfile)
            if end_reached:
                break

            if is_relevant:
                relevant_logfile.write(line)

            if "--- Results ---" in line:
                is_relevant = True

            counter, total, progress_bar = create_and_update_progress_bar_phase2(
                line, counter, total, progress_bar, "Checking assertion(s)"
            )


def main():
    args = parse_args()
    global logger
    logger.setLevel(args.log_level)

    if args.log:
        handle_log(args)

    args.input = os.path.abspath(args.input)
    req_folder = os.path.dirname(args.input)
    args.req_basename, req_extension = os.path.splitext(os.path.basename(args.input))
    req_filename = args.req_basename + req_extension

    if not args.output:
        args.output = req_folder

    if not args.tmp_dir:
        args.tmp_dir = os.path.join(req_folder, "reqcheck")

    create_dirs_if_necessary(args, [args.output, args.tmp_dir])

    args.reqcheck_log = os.path.join(req_folder, req_filename + '.log')
    args.testgen_log = os.path.join(req_folder, req_filename + '.testgen.log')

    args.reqcheck_relevant_log = os.path.join(args.output, req_filename + '.relevant.log')
    args.testgen_relevant_log = os.path.join(args.output, req_filename + '.testgen.relevant.log')

    if args.analyze_requirements:
        handle_analyze_requirements(args)

    if args.generate_tests:
        handle_generate_tests(args)

    # TODO: Print results


# regex for progress bars
re_phase1_start = SimpleMatcher(r'.*Computing rt-inconsistency assertions for (\d+) subsets')
re_phase1_progress = SimpleMatcher(r'.*?(\d+) subsets remaining')
re_phase1_end = SimpleMatcher(r'.*?(\d+) checks, \d+ trivial consistent, \d+ non-trivial')
re_phase2_start = SimpleMatcher(r'.* trace abstraction to program that has (\d+) error locations')
re_phase2_description = SimpleMatcher(
    r'.*======== Iteration 0==of CEGAR loop == myProcedureErr\d+ASSERT_VIOLATION(\w+)for(.*?)========')
re_phase2_progress = SimpleMatcher(
    r'.*Result for error location myProcedureErr\d+ASSERT_VIOLATION\w+(.*?) was (\w+) \((\d+)/\d+\)')
re_plugin_end = SimpleMatcher(r'.*------------------------ END.*')

LOG_FORMAT_STR = '%(message)s'
logging.basicConfig(format=LOG_FORMAT_STR)
logger = logging.getLogger(__package__)
ExitCode = _ExitCode()

if __name__ == "__main__":
    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)
    if platform.system() != 'Windows':
        # just ignore pipe exceptions
        signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    main()
