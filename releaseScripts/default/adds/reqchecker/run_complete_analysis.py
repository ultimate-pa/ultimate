#!/usr/bin/env python3

import argparse
import atexit
import logging
import os
import pathlib
import platform
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import traceback
from typing import Optional, List

from tqdm import tqdm


class _ExitCode:
    """
    Specify a named exit code for global usage.
    """

    _exit_codes = [
        "SUCCESS",
        "FAIL_NO_ACTION",
        "FAIL_SIGNAL",
        "FAIL_FILE_AS_DIR",
        "FAIL_SUBPROCESS",
        "FAIL_MISSING_LOGFILE",
        "FAIL_EXCEPTION",
        "USER_DO_NOT_CREATE_DIR",
        "USER_DO_NOT_DELETE_DIR",
        "USER_DO_NOT_DELETE_FILE",
    ]

    def __init__(self):
        pass

    def __getattr__(self, name):
        if name in _ExitCode._exit_codes:
            return _ExitCode._exit_codes.index(name)
        raise AttributeError(f"Exit code {name} not found")


class SimpleMatcher:
    def __init__(self, regex):
        self.__regex = re.compile(regex)
        self.__match = None

    def match(self, line):
        self.__match = self.__regex.match(line)
        return bool(self.__match)

    def group(self, i):
        return self.__match.group(i)


class ExplodeAssertions:
    """
    Convert (assert (and o1 o2 ...)) to (assert o1) (assert o2) (assert ...) in .smt2 files
    """

    def __init__(self):
        pass

    def __get_top_operands(self, s):
        operands = []
        pstack = []
        no_par_op = ""

        for i, c in enumerate(s):
            if c == "(":
                pstack.append(i)
                if no_par_op != "":
                    operands.append(no_par_op.strip())
                    no_par_op = ""
            elif c == ")":
                if len(pstack) == 0:
                    raise IndexError(
                        f"No matching closing parenthesis at index {str(i)} for input line {s}"
                    )
                j = pstack.pop()
                if len(pstack) == 0:
                    operands.append(s[j : i + 1])
            elif c == " ":
                if len(pstack) == 0 and no_par_op != "":
                    operands.append(no_par_op.strip())
                    no_par_op = ""
            elif len(pstack) == 0:
                # we have a top level operand without parenthesis ;
                # we want to capture all from now until the first opening parenthesis in one operand
                no_par_op += c

        if len(pstack) > 0:
            raise IndexError(
                f"No matching opening parenthesis at index {str(pstack.pop())} for input line {s}"
            )
        if no_par_op != "":
            operands.append(no_par_op.strip())
        return operands

    def split_and(self, s):
        if s.startswith("(and"):
            rtr = []
            for operand in self.__get_top_operands(s[5 : len(s) - 1]):
                rtr = rtr + self.split_and(operand)
            return rtr
        else:
            return [s]

    def explode(self, input_smt_file, output_smt_file):
        if input_smt_file == output_smt_file:
            raise ValueError("Input and output file must be different")

        with open(input_smt_file, encoding="utf-8") as f, open(
            output_smt_file, "w", encoding="utf-8"
        ) as o:
            for line in f.readlines():
                if line.startswith("(assert (!"):
                    m = re.search(r"\(assert \(! (.*?) :named (.*?)\)\)", line)
                    formula = m.group(1)
                    name = m.group(2)
                    if formula == "true":
                        continue
                    asserts = self.split_and(formula)
                    if len(asserts) == 1:
                        o.write(f"(assert (! {asserts[0]} :named {name}))\n")
                    else:
                        i = 0
                        for sub in asserts:
                            o.write(
                                f'(assert (! {sub} :named {name + "_" + str(i)}))\n'
                            )
                            i = i + 1
                else:
                    o.write(line)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="This script is a wrapper script for Ultimate ReqAnalyzer. "
        "It shows progress and handles the execution of test generation and requirement analysis."
    )

    parser.add_argument(
        "input", metavar="<file>", type=check_file, help="Requirement file. (*.req)"
    )

    parser.add_argument(
        "--log",
        metavar="<file>",
        nargs=1,
        default=None,
        help="Log the output of the script to <file>",
    )
    parser.add_argument(
        "--log-level",
        dest="log_level",
        nargs="?",
        default=logging.INFO,
        choices=["DEBUG", "INFO", "ERROR", "WARN"],
        help="Log level of the script. Default: INFO",
    )
    parser.add_argument(
        "-f", "--force", action="store_true", help="Suppress all prompts"
    )

    parser.add_argument(
        "-o",
        "--output",
        metavar="<dir>",
        type=str,
        default=None,
        help="Folder where reports (*.relevant.log, vacuous .req subsets, etc.) are saved. "
        "Default: In directory log_<input>/ besides input file.",
    )

    parser.add_argument(
        "--tmp-dir",
        metavar="<dir>",
        type=str,
        default=None,
        help="Folder where full Ultimate logs and .smt2 dumps are saved. "
        "Default: In directory reqcheck_<input>_tmp/ besides input file.",
    )

    parser.add_argument(
        "-ar",
        "--analyze-requirements",
        action="store_true",
        help="Run requirement analysis.",
    )
    parser.add_argument(
        "-gt", "--generate-tests", action="store_true", help="Run test generation."
    )

    parser.add_argument(
        "--rt-inconsistency-range",
        type=int,
        default=2,
        help="The amount of requirements which are checked together for RT-inconsistency. Default: 2",
    )
    parser.add_argument(
        "--timeout-per-assertion",
        type=int,
        default=900,
        help="Amount of seconds until analysis of an assertion is timed out. Default: 900",
    )

    config_files = parser.add_argument_group(
        title="Ultimate location and configuration files",
        description="Control the location of Ultimate ReqChecker itself and"
        " various config files. "
        "You should normally never change these settings. ",
    )
    config_files.add_argument(
        "--ultimate-dir",
        type=check_dir,
        metavar="<file>",
        default=".",
        help="The path to Ultimate ReqAnalyzer." "Default: .",
    )

    config_files.add_argument(
        "--reqcheck-toolchain",
        type=check_file,
        metavar="<file>",
        default="config/ReqCheck.xml",
        help="The Ultimate toolchain file (.xml) that will be used during requirements checking."
        "Default: config/ReqCheck.xml",
    )

    config_files.add_argument(
        "--reqcheck-settings",
        type=check_file,
        metavar="<file>",
        default="config/ReqCheck-nonlin.epf",
        help="The Ultimate settings file (.epf) that will be used during requirements checking."
        "Default: config/ReqCheck-nonlin.epf",
    )

    config_files.add_argument(
        "--testgen-toolchain",
        type=check_file,
        metavar="<file>",
        default="config/ReqToTest.xml",
        help="The Ultimate toolchain file (.xml) that will be used during test generation."
        "Default: config/ReqToTest.xml",
    )

    config_files.add_argument(
        "--testgen-settings",
        type=check_file,
        metavar="<file>",
        default="config/ReqCheck-ReqToTest.epf",
        help="The Ultimate settings file (.epf) that will be used during test generation."
        "Default: config/ReqCheck-ReqToTest.epf",
    )

    config_files.add_argument(
        "--z3",
        type=str,
        metavar="<file>",
        default=None,
        help="A path to a working z3 binary." "Default: <ultimate-dir>/z3",
    )

    args = parser.parse_args()

    if not args.analyze_requirements and not args.generate_tests:
        parser.print_help()
        sys.exit(ExitCode.FAIL_NO_ACTION)

    return args


def set_complex_arg_defaults(args):
    args.input = os.path.abspath(args.input)
    req_folder = os.path.dirname(args.input)
    args.req_basename, req_extension = os.path.splitext(os.path.basename(args.input))
    req_filename = args.req_basename + req_extension
    if not args.output:
        args.output = os.path.join(req_folder, "log_" + args.req_basename)
    if not args.tmp_dir:
        args.tmp_dir = os.path.join(
            req_folder, "reqcheck_" + args.req_basename + "_tmp"
        )
    if not args.z3:
        if platform.system() == "Windows":
            args.z3 = os.path.join(os.path.abspath(args.ultimate_dir), "z3.exe")
        else:
            args.z3 = os.path.join(os.path.abspath(args.ultimate_dir), "z3")
        if not os.path.exists(args.z3):
            raise ValueError(
                f'z3 instance does not exists at "{args.z3}". Consider setting "--z3".'
            )

    create_dirs_if_necessary(args, [args.output, args.tmp_dir])
    args.reqcheck_log = os.path.join(req_folder, req_filename + ".log")
    args.testgen_log = os.path.join(req_folder, req_filename + ".testgen.log")
    args.reqcheck_relevant_log = os.path.join(
        args.output, req_filename + ".relevant.log"
    )
    args.testgen_relevant_log = os.path.join(
        args.output, req_filename + ".testgen.relevant.log"
    )
    return args


def token_string_or_file(arg):
    if not os.path.exists(arg):
        return arg
    else:
        return open(arg, "r").read().strip()


def check_dir(arg):
    if not os.path.exists(arg):
        msg = f"Directory {arg} does not exist"
        print(msg)
        raise argparse.ArgumentError(message=msg)
    return arg


def check_file(arg):
    if not os.path.isfile(arg):
        msg = f"{arg} does not exist or is not a file"
        print(msg)
        raise argparse.ArgumentError(message=msg)
    return arg


def create_dirs_if_necessary(args, dirs):
    for d in dirs:
        if os.path.isdir(d):
            continue

        if not confirm_if_necessary(
            args, f"Directory {d} does not exist, should I create it?"
        ):
            sys.exit(ExitCode.USER_DO_NOT_CREATE_DIR)

        os.makedirs(d)


def delete_dir_if_necessary(args, d):
    if os.path.isfile(d):
        logging.fatal(f"Will not delete file {d}")
        sys.exit(ExitCode.FAIL_FILE_AS_DIR)

    if not os.path.isdir(d):
        return

    if not confirm_if_necessary(args, f"Directory {d} exists, should I delete it?"):
        sys.exit(ExitCode.USER_DO_NOT_DELETE_DIR)

    shutil.rmtree(d)


def delete_file_if_necessary(args, file):
    if not os.path.isfile(file):
        return

    if not confirm_if_necessary(args, f"File {file} exists, should I delete it?"):
        sys.exit(ExitCode.USER_DO_NOT_DELETE_FILE)

    os.remove(file)


def init_child_process():
    new_umask = 0o022
    os.umask(new_umask)


def call(call_args: Optional[List[str]]):
    if call_args is None:
        call_args = []

    try:
        if platform.system() == "Linux":
            child_process = subprocess.Popen(
                call_args,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                shell=False,
                preexec_fn=init_child_process,
            )
        else:
            child_process = subprocess.Popen(
                call_args,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                shell=False,
            )
    except Exception as ex:
        logger.fatal(f"Error trying to open subprocess {str(call_args)}")
        logger.fatal(ex)
        sys.exit(ExitCode.FAIL_SUBPROCESS)
    global running_processes
    running_processes += [child_process]
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
        prompt = "Confirm"
    if default_response:
        prompt = f'{prompt} [{"y"}]|{"n"}: '
    else:
        prompt = f'{prompt} [{"n"}]|{"y"}: '

    while True:
        ans = input(prompt)
        if not ans:
            return default_response
        if ans not in ["y", "Y", "n", "N"]:
            print("please enter y or n.")
            continue
        if ans == "y" or ans == "Y":
            return True
        if ans == "n" or ans == "N":
            return False


def confirm_if_necessary(args, prompt: str = None, default_response: bool = False):
    if args.force:
        return True
    return confirm(prompt, default_response)


def signal_handler(sig, frame):
    print(f"Killed by {sig}")
    cleanup_subprocesses()
    sys.exit(ExitCode.FAIL_SIGNAL)


def cleanup_subprocesses():
    for subp in running_processes:
        print(f"Killing left-over subprocess {subp.pid}")
        subp.kill()


def update_line(subp, logfile=None):
    line = subp.stdout.readline().decode("utf-8", "ignore")

    subp.poll()
    if subp.returncode is not None and not line:
        if subp.returncode == 0:
            logger.debug("Execution finished normally")
        else:
            logger.error(
                f'Execution of {" ".join(subp.args)} (PID {subp.pid}) finished with exit code {str(subp.returncode)}'
            )
        global running_processes
        if running_processes:
            running_processes.remove(subp)
        return None, True
    if logfile:
        logfile.write(line.rstrip() + "\n")
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
        progress_bar.set_description("Phase 1: Creating rt-inconsistency checks")
    elif re_phase1_progress.match(line):
        finished = total - int(re_phase1_progress.group(1))
        progress_bar.update(finished - counter)
        counter = finished
    elif re_phase1_end.match(line):
        progress = int(re_phase1_end.group(1))
        if progress == total and counter < total:
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
            f"{desc} {re_phase2_description.group(1)} for requirement {re_phase2_description.group(2)}"
        )
    elif re_phase2_progress.match(line):
        progress = int(re_phase2_progress.group(3))
        counter += progress
        progress_bar.update(1)
    else:
        progress_bar = update_progress_bar_plugin_end(line, progress_bar)
    return counter, total, progress_bar


def make_z3_compatible(filename):
    # sed-like replacement
    repls = [
        (re.compile(r"\(get-interpolants.*"), "(get-unsat-core)"),
        (re.compile(r".*produce-interpolants.*"), ""),
        (re.compile(r".*:interpolant-check-mode.*"), ""),
        (re.compile(r".*:proof-transformation.*"), ""),
        (re.compile(r".*:array-interpolation.*"), ""),
    ]

    with tempfile.NamedTemporaryFile(mode="w", delete=False) as tmp_file:
        with open(filename) as src_file:
            for line in src_file:
                for pattern, repl in repls:
                    line = pattern.sub(repl, line)
                tmp_file.write(line)

    shutil.copystat(filename, tmp_file.name)
    shutil.move(tmp_file.name, filename)


def extract_vacuity_reasons(args, dump_folder, vacuous_reqs):
    # collect all vacuous reqs from Ultimate results
    re_vac_req = SimpleMatcher(r".*ReqCheckFailResult.*Requirement (.*?) is vacuous.*")
    vac_req_ids = set()
    for line in vacuous_reqs:
        if re_vac_req.match(line):
            vac_req_ids.add(re_vac_req.group(1))

    # collect all req_ids from req file
    re_req_id = SimpleMatcher(r"^(\w*?):.*$")
    with open(args.input, "r") as req_file:
        req_ids = set()
        for line in req_file.readlines():
            if re_req_id.match(line):
                req_ids.add(re_req_id.group(1))
    logger.debug(f"Identified requirement ids {req_ids}")

    # extract vacuity reasons for each vacuous requirement
    vac_req_ids_pb = tqdm(vac_req_ids)
    for vac_req_id in vac_req_ids_pb:
        vac_req_ids_pb.set_description(
            ("Phase 3: Extracting vacuity reasons for {}".format(vac_req_id))
        )
        relevant_req_ids = extract_vacuity_reason(
            args, dump_folder, req_ids, vac_req_id
        )

        # create new .req file only containing relevant requirements from LBE
        tmp_req_file_lbe = os.path.join(
            dump_folder, args.req_basename + "." + vac_req_id + ".lbe.vac.req"
        )
        extract_vacuity_project_reqs(args, req_ids, relevant_req_ids, tmp_req_file_lbe)

        # run ultimate with small block encoding (SBE) on new .req file
        dump_folder_sbe = extract_vacuity_run_ultimate_sbe(
            args, tmp_req_file_lbe, vac_req_id, vac_req_ids_pb
        )

        # re-analyze the results of the SBE ultimate run
        relevant_req_ids = extract_vacuity_reason(
            args, dump_folder_sbe, req_ids, vac_req_id
        )

        # create new .req file only containing relevant requirements from SBE
        tmp_req_file_sbe = os.path.join(
            dump_folder, args.req_basename + "." + vac_req_id + ".vac.req"
        )
        extract_vacuity_project_reqs(args, req_ids, relevant_req_ids, tmp_req_file_sbe)

        # move the SBE .req file to the log folder
        shutil.move(
            tmp_req_file_sbe,
            os.path.join(args.output, os.path.basename(tmp_req_file_sbe)),
        )


def extract_vacuity_project_reqs(args, req_ids, relevant_req_ids, target_req_file):
    irrelevant_req_ids = req_ids.difference(relevant_req_ids)
    with open(args.input, "r") as source, open(target_req_file, "w") as target:
        for line in source:
            if any(req_id in line for req_id in irrelevant_req_ids):
                continue
            target.write(line)


def extract_vacuity_run_ultimate_sbe(args, tmp_req_file, vac_req_id, pb):
    dump_folder_sbe = os.path.join(
        args.tmp_dir, "dump_sbe", args.req_basename + "_" + vac_req_id
    )
    pathlib.Path(dump_folder_sbe).mkdir(parents=True, exist_ok=True)
    logfile_name = os.path.join(dump_folder_sbe, "ultimate.log")
    cmd = create_common_ultimate_cli_args(
        args, args.reqcheck_toolchain, args.reqcheck_settings, tmp_req_file
    )
    cmd += create_reqchecker_cli_args(args, dump_folder_sbe)
    cmd += [
        "--rcfgbuilder.size.of.a.code.block",
        "SingleStatement",
        "--pea2boogie.check.rt-inconsistency",
        "false",
    ]
    ultimate_process = call(cmd)
    pb.set_description(
        f"Phase 3: Running ReqChecker for vacuity analysis of {vac_req_id} with PID {ultimate_process.pid}"
    )
    with open(logfile_name, "w") as logfile:
        while True:
            line, end_reached = update_line(ultimate_process, logfile)
            if end_reached:
                break
    return dump_folder_sbe


def extract_vacuity_reason(args, dump_folder, req_ids, vac_req_id):
    # find .smt2 files that were dumped during the analysis for vac_req_id
    smt_files = []
    for file in os.listdir(dump_folder):
        name = os.path.basename(file)
        if file.endswith(".smt2") and "VAC" in name and vac_req_id in name:
            logger.debug(f"Collected {file} for {vac_req_id}")
            smt_files += [os.path.join(dump_folder, file)]
    # compute the set of relevant requirements for each .smt2 file
    relevant_req_ids = set()
    for smt_file in smt_files:
        tmp_smt_filename = smt_file + ".lbe"
        # explode this file (convert top-level conjunction in assert in many separate asserts)
        ExplodeAssertions().explode(smt_file, tmp_smt_filename)

        # change various SMTLIB artifacts of Ultimate s.t. the file becomes compatible with z3 and computes the
        # unsat core instead of interpolants
        make_z3_compatible(tmp_smt_filename)

        # execute z3 on the file
        relevant_lines = extract_vacuity_run_z3(args, tmp_smt_filename)

        # extract ssa's that are in the unsat core from line after unsat
        ssas = set(
            [
                ssa.rstrip()
                for rel_line in relevant_lines
                for ssa in rel_line.replace("(", "").replace(")", "").split(" ")
            ]
        )

        logger.debug(f"Looking for unsat core SSAs {ssas} in {tmp_smt_filename}")

        with open(tmp_smt_filename, "r") as tmp_smt_file:
            for assertion in [
                line
                for line in tmp_smt_file.readlines()
                if any(ssa in line for ssa in ssas)
            ]:
                relevant_req_ids.update(
                    [req_id for req_id in req_ids if req_id in assertion]
                )

    logger.debug(
        f"Found {len(relevant_req_ids)} requirements relevant for vacuity of {vac_req_id}"
    )
    logger.debug(f"Relevant requirements for {vac_req_id} are {relevant_req_ids}")
    if vac_req_id not in relevant_req_ids:
        logger.error(
            f"{vac_req_id} is not in the list of relevant requirement ids {relevant_req_ids}, something is wrong!"
        )
    return relevant_req_ids


def extract_vacuity_run_z3(args, tmp_smt_filename):
    z3 = call([args.z3, tmp_smt_filename])
    logger.debug("Running z3 with PID {} on {}".format(z3.pid, tmp_smt_filename))

    line = None
    relevant_lines = []
    while True:
        last_line = line
        line, end_reached = update_line(z3)
        if end_reached:
            break
        logger.debug(line.rstrip())

        if last_line and "unsat" in last_line:
            relevant_lines += [line]
    return relevant_lines


def create_common_ultimate_cli_args(args, toolchain, settings, input_file):
    return [
        "java",
        "-Dosgi.configuration.area=config/",
        "-Xmx100G",
        "-Xss4m",
        "-jar",
        "plugins/org.eclipse.equinox.launcher_1.5.800.v20200727-1323.jar",
        "-tc",
        toolchain,
        "-s",
        settings,
        "-i",
        input_file,
        "--core.print.statistic.results",
        "false",
        "--traceabstraction.limit.analysis.time",
        str(args.timeout_per_assertion),
    ]


def create_reqchecker_cli_args(args, dump_folder):
    return [
        "--traceabstraction.dump.smt.script.to.file",
        "true",
        "--traceabstraction.to.the.following.directory",
        dump_folder,
        "--pea2boogie.always.use.all.invariants.during.rt-inconsistency.checks",
        "true",
        "--pea2boogie.check.vacuity",
        "true",
        "--pea2boogie.check.consistency",
        "true",
        "--pea2boogie.report.trivial.rt-consistency",
        "false",
        "--pea2boogie.use.epsilon.transformation.during.rt-inconsistency.check",
        "false",
        "--pea2boogie.rt-inconsistency.range",
        str(args.rt_inconsistency_range),
    ]


def handle_log(args):
    global logger
    handler = logging.FileHandler(args.log)
    handler.setLevel(args.log_level)
    log_formatter = logging.Formatter(
        "%(asctime)s %(name)-8s %(levelname)-6s: %(message)s"
    )
    handler.setFormatter(log_formatter)
    logger.addHandler(handler)


def handle_analyze_requirements(args):
    logger.info("Running ReqChecker")

    os.chdir(args.ultimate_dir)
    delete_dir_if_necessary(args, args.tmp_dir)
    dump_folder = os.path.join(args.tmp_dir, "dump", args.req_basename)
    logger.info(f"Creating dump folder {dump_folder}")
    pathlib.Path(dump_folder).mkdir(parents=True, exist_ok=True)
    delete_file_if_necessary(args, args.reqcheck_log)

    logger.info(f"Analyzing {args.input}")
    logger.info(f"Using logfile {args.reqcheck_log}")

    cmd = create_common_ultimate_cli_args(
        args, args.reqcheck_toolchain, args.reqcheck_settings, args.input
    )
    cmd += create_reqchecker_cli_args(args, dump_folder)
    cmd += [
        "--rcfgbuilder.size.of.a.code.block",
        "LoopFreeBlock",
        "--pea2boogie.check.rt-inconsistency",
        "true",
    ]

    ultimate_process = call(cmd)

    relevant_log = []
    relevant_results = [
        "ReqCheckSuccessResult",
        "ReqCheckFailResult",
        "ReqCheckRtInconsistentResult",
        "RequirementInconsistentErrorResult",
    ]

    progress_bar = None

    phase1_counter = 0
    phase1_total = 0
    phase2_counter = 0
    phase2_total = 0
    logger.info(f"Started ReqChecker with PID {ultimate_process.pid}")
    with open(args.reqcheck_log, "w", buffering=1) as logfile:
        line = ""
        current_result = []
        collect = False
        while True:
            line, end_reached = update_line(ultimate_process, logfile)
            if end_reached:
                break

            if not line or line.startswith("  - "):
                collect = False

            if not collect and current_result:
                relevant_log += current_result
                current_result = []

            if collect or any([keyword in line for keyword in relevant_results]):
                collect = True
                current_result += [line.rstrip() + "\n"]

            # show and update progress bars
            (
                phase1_counter,
                phase1_total,
                progress_bar,
            ) = create_and_update_progress_bar_phase1(
                line, phase1_counter, phase1_total, progress_bar
            )
            (
                phase2_counter,
                phase2_total,
                progress_bar,
            ) = create_and_update_progress_bar_phase2(
                line,
                phase2_counter,
                phase2_total,
                progress_bar,
                "Phase 2: Checking assertion(s)",
            )

    logger.info(f"Extracting results to {args.reqcheck_relevant_log}")
    with open(args.reqcheck_relevant_log, "w+") as relevant_logfile:
        relevant_logfile.write("".join(relevant_log))

    # Postprocess results with vacuity extractor.
    # Note the spaces
    vacuous_reqs = [line for line in relevant_log if "is vacuous" in line]
    if any(vacuous_reqs):
        extract_vacuity_reasons(args, dump_folder, vacuous_reqs)
    else:
        logger.info("No vacuities found.")


def handle_generate_tests(args):
    logger.info("Running test generation")
    logger.info(f"Using logfile {args.testgen_log}")

    cmd = create_common_ultimate_cli_args(
        args, args.testgen_toolchain, args.testgen_settings, args.input
    )
    cmd += [
        "--rcfgbuilder.simplify.code.blocks",
        "false",
        "--rcfgbuilder.size.of.a.code.block",
        "LoopFreeBlock",
        "--rcfgbuilder.add.additional.assume.for.each.assert",
        "false",
    ]

    ultimate_process = call(cmd)

    is_relevant = False
    counter = 0
    total = 0
    progress_bar = None
    logger.info(f"Started ReqChecker with PID {ultimate_process.pid}")
    with open(args.testgen_log, "w") as logfile, open(
        args.testgen_relevant_log, "w"
    ) as relevant_logfile:
        while True:
            line, end_reached = update_line(ultimate_process, logfile)
            if end_reached:
                break

            if is_relevant:
                relevant_logfile.write(line.rstrip() + "\n")

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

    args = set_complex_arg_defaults(args)

    if args.analyze_requirements:
        handle_analyze_requirements(args)

    if args.generate_tests:
        handle_generate_tests(args)

    # TODO: Print results


# regex for progress bars
re_phase1_start = SimpleMatcher(
    r".*Computing rt-inconsistency assertions for (\d+) subsets"
)
re_phase1_progress = SimpleMatcher(r".*?(\d+) subsets remaining")
re_phase1_end = SimpleMatcher(
    r".*?(\d+) checks, \d+ trivial consistent, \d+ non-trivial"
)
re_phase2_start = SimpleMatcher(
    r".* trace abstraction to program that has (\d+) error locations"
)
re_phase2_description = SimpleMatcher(
    r".* === Iteration \d === Targeting myProcedureErr\d+ASSERT_VIOLATION(\w+)for(.*?) ==="
)
#  r".*Result for error location myProcedureErr\d+ASSERT_VIOLATION\w+(.*?) was (\w+) \((\d+)/\d+\)"
re_phase2_progress = SimpleMatcher(
    r".* Registering result (\w+) for location myProcedureErr\d+ASSERT_VIOLATION\w+(.*?) \((\d+) of \d+ remaining\)"
)
re_plugin_end = SimpleMatcher(r".*------------------------ END.*")

# global variables
LOG_FORMAT_STR = "%(message)s"
logging.basicConfig(format=LOG_FORMAT_STR)
logger = logging.getLogger(__package__)
ExitCode = _ExitCode()
running_processes = []

if __name__ == "__main__":
    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)
    if platform.system() != "Windows":
        # just ignore pipe exceptions
        signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    atexit.register(cleanup_subprocesses)
    try:
        main()
    except SystemExit:
        pass
    except:
        print(traceback.format_exc())
        sys.exit(ExitCode.FAIL_EXCEPTION)
