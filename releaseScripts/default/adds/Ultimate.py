#!/usr/bin/env python3

from __future__ import print_function

import argparse
import fnmatch
import glob
import os
import platform
import re
import shutil
import signal
import subprocess
import sys
import xml.etree.ElementTree as elementtree
from stat import ST_MODE
from functools import lru_cache

# quoting style is important here
# fmt: off
version = '4f54f8f5'
toolname = 'Automizer'
# fmt: on

write_ultimate_output_to_file = True
output_file_name = "Ultimate.log"
error_path_file_name = "UltimateCounterExample.errorpath"
ultimatedir = os.path.dirname(os.path.realpath(__file__))
configdir = os.path.join(ultimatedir, "config")
datadir = os.path.join(ultimatedir, "data")
witnessdir = ultimatedir
witnessname = "witness"
enable_assertions = False

# special strings in ultimate output
unsupported_syntax_errorstring = "ShortDescription: Unsupported Syntax"
incorrect_syntax_errorstring = "ShortDescription: Incorrect Syntax"
type_errorstring = "Type Error"
witness_errorstring = "InvalidWitnessErrorResult"
exception_errorstring = "ExceptionOrErrorResult"
safety_string = "Ultimate proved your program to be correct"
all_spec_string = "AllSpecificationsHoldResult"
unsafety_string = "Ultimate proved your program to be incorrect"
mem_deref_false_string = "pointer dereference may fail"
mem_deref_false_string_2 = "array index can be out of bounds"
mem_free_false_string = "free of unallocated memory possible"
mem_memtrack_false_string = "not all allocated memory was freed"
termination_false_string = "Found a nonterminating execution for the following lasso shaped sequence of statements"
termination_true_string = "TerminationAnalysisResult: Termination proven"
ltl_false_string = "execution that violates the LTL property"
ltl_true_string = "Buchi Automizer proved that the LTL property"
error_path_begin_string = "We found a FailurePath:"
termination_path_end = "End of lasso representation."
overflow_false_string = "overflow possible"
data_race_found_string = "DataRaceFoundResult"
data_race_error_path_begin_string = "The following path leads to a data race"


class _PropParser:
    prop_regex = re.compile(
        "^\s*CHECK\s*\(\s*init\s*\((.*)\)\s*,\s*LTL\((.*)\)\s*\)\s*$", re.MULTILINE
    )
    funid_regex = re.compile("\s*(\S*)\s*\(.*\)")
    word_regex = re.compile("\b[^\W\d_]+\b")
    forbidden_words = [
        "valid-free",
        "valid-deref",
        "valid-memtrack",
        "end",
        "overflow",
        "call",
        "data-race",
    ]

    def __init__(self, propfile):
        self.propfile = propfile
        self.content = open(propfile, "r").read()
        self.termination = False
        self.mem_deref = False
        self.mem_memtrack = False
        self.mem_free = False
        self.overflow = False
        self.reach = False
        self.ltl = False
        self.init = None
        self.ltlformula = None
        self.mem_cleanup = False
        self.data_race = False

        for match in self.prop_regex.finditer(self.content):
            init, formula = match.groups()

            fun_match = self.funid_regex.match(init)
            if not fun_match:
                raise RuntimeError("No init specified in this check")
            if self.init and self.init != fun_match.group(1):
                raise RuntimeError(
                    "We do not support multiple and different init functions (have seen {0} and {1}".format(
                        self.init, fun_match.group(1)
                    )
                )
            self.init = fun_match.group(1)

            if (
                formula == "G ! call(reach_error())"
                or formula == "G ! call(__VERIFIER_error())"
            ):
                self.reach = True
            elif formula == "G valid-free":
                self.mem_free = True
            elif formula == "G valid-deref":
                self.mem_deref = True
            elif formula == "G valid-memtrack":
                self.mem_memtrack = True
            elif formula == "F end":
                self.termination = True
            elif formula == "G ! overflow":
                self.overflow = True
            elif formula == "G valid-memcleanup":
                self.mem_cleanup = True
            elif formula == "G ! data-race":
                self.data_race = True
            elif not check_string_contains(
                self.word_regex.findall(formula), self.forbidden_words
            ):
                # its ltl
                if self.ltl:
                    raise RuntimeError(
                        "We support only one (real) LTL property per .prp file (have seen {0} and {1}".format(
                            self.ltlformula, formula
                        )
                    )
                self.ltl = True
                self.ltlformula = formula
            else:
                raise RuntimeError("The formula {0} is unknown".format(formula))

    def get_init_method(self):
        return self.init

    def get_content(self):
        return self.content

    def is_termination(self):
        return self.termination

    def is_only_mem_deref(self):
        return self.mem_deref and not self.mem_free and not self.mem_memtrack

    def is_any_mem(self):
        return self.mem_deref or self.mem_free or self.mem_memtrack or self.mem_cleanup

    def is_mem_deref_memtrack(self):
        return self.mem_deref and self.mem_memtrack

    def is_mem_memtrack(self):
        return self.mem_memtrack

    def is_mem_cleanup(self):
        return self.mem_cleanup

    def is_overflow(self):
        return self.overflow

    def is_reach(self):
        return self.reach

    def is_ltl(self):
        return self.ltl

    def get_ltl_formula(self):
        return self.ltlformula

    def is_data_race(self):
        return self.data_race


class _AbortButPrint(Exception):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return repr(self.value)


class _CallFailed(Exception):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return repr(self.value)


class _ExitCode:
    _exit_codes = [
        "SUCCESS",
        "FAIL_OPEN_SUBPROCESS",
        "FAIL_NO_INPUT_FILE",
        "FAIL_NO_WITNESS_TO_VALIDATE",
        "FAIL_MULTIPLE_FILES",
        "FAIL_NO_TOOLCHAIN_FOUND",
        "FAIL_NO_SETTINGS_FILE_FOUND",
        "FAIL_ULTIMATE_ERROR",
        "FAIL_SIGNAL",
        "FAIL_NO_JAVA",
        "FAIL_NO_SPEC",
        "FAIL_NO_ARCH",
        "FAIL_WRONG_WITNESS_TYPE",
    ]

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


@lru_cache(maxsize=1)
def get_java():
    if os.name == "nt":  # Windows
        candidates = [
            "java.exe",
            "C:\\Program Files\\Java\\jdk-11\\bin\\java.exe",
            "C:\\Program Files\\Eclipse Adoptium\\jdk-11*-hotspot\\bin\\java.exe",
        ]
    else:  # Unix-like
        candidates = [
            "java",
            "/usr/bin/java",
            "/opt/oracle-jdk-bin-*/bin/java",
            "/opt/openjdk-*/bin/java",
            "/usr/lib/jvm/java-*-openjdk-amd64/bin/java",
        ]

    candidates_extended = []
    for c in candidates:
        if "*" in c:
            candidates_extended += glob.glob(c)
        else:
            candidates_extended += [c]

    pattern = r'"(\d+\.\d+).*"'
    for c in candidates_extended:
        candidate = shutil.which(c)
        if not candidate:
            continue

        process = call_desperate([candidate, "-version"])
        while True:
            line = process.stdout.readline().decode("utf-8", "ignore")
            if not line:
                break
            match = re.search(pattern, line)
            if match:
                java_version = match.groups()[0]
                java_version = java_version.split(".")[0]
                java_version = int(java_version)
                if java_version == 11:
                    return candidate
    print_err("Did not find Java 11 in known paths")
    sys.exit(ExitCode.FAIL_NO_JAVA)


def create_ultimate_base_call():
    ultimate_bin = [
        get_java(),
        "-Dosgi.configuration.area=" + os.path.join(datadir, "config"),
        "-Xmx15G",
        "-Xms4m",
    ]

    if enable_assertions:
        ultimate_bin = ultimate_bin + ["-ea"]

    ultimate_bin = ultimate_bin + [
        "-jar",
        os.path.join(
            ultimatedir,
            "plugins/org.eclipse.equinox.launcher_1.5.800.v20200727-1323.jar",
        ),
        "-data",
        "@noDefault",
        "-ultimatedata",
        datadir,
    ]

    return ultimate_bin


def search_config_dir(searchstring):
    for root, dirs, files in os.walk(configdir):
        for name in files:
            if fnmatch.fnmatch(name, searchstring):
                return os.path.join(root, name)
        break
    print(
        "No suitable file found in config dir {0} using search string {1}".format(
            configdir, searchstring
        )
    )
    return


def contains_overapproximation_result(line):
    triggers = [
        "Reason: overapproximation of",
        "Reason: overapproximation of bitwiseAnd",
        "Reason: overapproximation of bitwiseOr",
        "Reason: overapproximation of bitwiseXor",
        "Reason: overapproximation of shiftLeft",
        "Reason: overapproximation of shiftRight",
        "Reason: overapproximation of bitwiseComplement",
    ]

    for trigger in triggers:
        if line.find(trigger) != -1:
            return True

    return False


def run_ultimate(ultimate_call, prop, verbose=False):
    print("Calling Ultimate with: " + " ".join(ultimate_call))
    if verbose:
        print("--- Real Ultimate output ---")

    ultimate_process = call_desperate(ultimate_call)

    result = "UNKNOWN"
    result_msg = "NONE"
    reading_error_path = False
    overapprox = False

    # poll the output
    ultimate_output = ""
    error_path = ""
    while True:
        line = ultimate_process.stdout.readline().decode("utf-8", "ignore")

        ultimate_process.poll()
        if ultimate_process.returncode is not None and not line:
            print("--- End real Ultimate output ---")
            if ultimate_process.returncode == 0:
                print("\nExecution finished normally")
            else:
                print(
                    "\nExecution finished with exit code "
                    + str(ultimate_process.returncode)
                )
            break

        if reading_error_path:
            error_path += line
        ultimate_output += line
        if verbose:
            sys.stdout.write(line)
        else:
            sys.stdout.write(".")
        sys.stdout.flush()
        if line.find(unsupported_syntax_errorstring) != -1:
            result = "ERROR: UNSUPPORTED SYNTAX"
        elif line.find(incorrect_syntax_errorstring) != -1:
            result = "ERROR: INCORRECT SYNTAX"
        elif line.find(type_errorstring) != -1:
            result = "ERROR: TYPE ERROR"
        elif line.find(witness_errorstring) != -1:
            result = "ERROR: INVALID WITNESS FILE"
        elif line.find(exception_errorstring) != -1:
            result = "ERROR: " + line[line.find(exception_errorstring) :]
            # hack to avoid errors with floats
            overapprox = True
        if not overapprox and contains_overapproximation_result(line):
            result = "UNKNOWN: Overapproximated counterexample"
            overapprox = True
        if prop.is_termination():
            result_msg = "TERM"
            if line.find(termination_true_string) != -1:
                result = "TRUE"
            if line.find(termination_false_string) != -1:
                result = "FALSE"
                reading_error_path = True
            if line.find(termination_path_end) != -1:
                reading_error_path = False
        elif prop.is_ltl():
            result_msg = "valid-ltl"
            if line.find(ltl_false_string) != -1:
                result = "FALSE"
                reading_error_path = True
            if line.find(ltl_true_string) != -1:
                result = "TRUE"
            if line.find(termination_path_end) != -1:
                reading_error_path = False
        elif prop.is_data_race():
            if line.find(data_race_found_string) != -1:
                result = "FALSE"
            if line.find(all_spec_string) != -1:
                result = "TRUE"
            if line.find(data_race_error_path_begin_string) != -1:
                blank_lines = 0
                reading_error_path = True
            if reading_error_path and line.strip() == "":
                if blank_lines < 1:
                    blank_lines += 1
                else:
                    reading_error_path = False
        else:
            if line.find(safety_string) != -1 or line.find(all_spec_string) != -1:
                result = "TRUE"
            if line.find(unsafety_string) != -1:
                result = "FALSE"
            if line.find(mem_deref_false_string) != -1:
                result_msg = "valid-deref"
            if line.find(mem_deref_false_string_2) != -1:
                result_msg = "valid-deref"
            if line.find(mem_free_false_string) != -1:
                result_msg = "valid-free"
            if line.find(mem_memtrack_false_string) != -1:
                if prop.is_mem_cleanup():
                    result_msg = "valid-memcleanup"
                else:
                    result_msg = "valid-memtrack"
            if line.find(overflow_false_string) != -1:
                result = "FALSE"
                result_msg = "OVERFLOW"
            if line.find(error_path_begin_string) != -1:
                reading_error_path = True
            if reading_error_path and line.strip() == "":
                reading_error_path = False

    return result, result_msg, overapprox, ultimate_output, error_path


def _init_child_process():
    new_umask = 0o022
    os.umask(new_umask)


def call_desperate(call_args):
    if call_args is None:
        call_args = []

    try:
        child_process = subprocess.Popen(
            call_args,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            shell=False,
            preexec_fn=None if is_windows() else _init_child_process,
        )
    except:
        print("Error trying to open subprocess " + str(call_args))
        sys.exit(ExitCode.FAIL_OPEN_SUBPROCESS)
    return child_process


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
        if isinstance(el, list) and not isinstance(el, (str, bytes)):
            for sub in flatten(el):
                yield sub
        else:
            yield el


def write_ltl(ltlformula):
    ltl_file_path = os.path.join(datadir, "ltlformula.ltl")
    with open(ltl_file_path, "wb") as ltl_file:
        ltl_file.write(ltlformula.encode("utf-8"))
    return ltl_file_path


def create_cli_settings(prop, validate_witness, architecture, c_file):
    # append detected init method
    ret = ["--cacsl2boogietranslator.entry.function", prop.get_init_method()]

    if prop.is_ltl():
        # we can neither validate nor produce witnesses in ltl mode,
        # so no additional arguments are required
        return ret

    # this is not ltl mode
    if validate_witness and not prop.is_termination():
        # we need to disable hoare triple generation as workaround for an internal bug
        # but only for reachability witness validation
        ret.append(
            "--traceabstraction.compute.hoare.annotation.of.negated.interpolant.automaton,.abstraction.and.cfg"
        )
        ret.append("false")
    elif not validate_witness:
        # we are not in validation mode, so we should generate a witness and need
        # to pass some things to the witness printer
        ret.append("--witnessprinter.witness.directory")
        ret.append(witnessdir)
        ret.append("--witnessprinter.witness.filename")
        ret.append(witnessname)
        ret.append("--witnessprinter.write.witness.besides.input.file")
        ret.append("false")

        ret.append("--witnessprinter.graph.data.specification")
        ret.append(prop.get_content())
        ret.append("--witnessprinter.graph.data.producer")
        ret.append(toolname)
        ret.append("--witnessprinter.graph.data.architecture")
        ret.append(architecture)
        ret.append("--witnessprinter.graph.data.programhash")

        sha = call_desperate(["sha256sum", c_file[0]])
        ret.append(sha.communicate()[0].split()[0].decode("utf-8", "ignore"))

    return ret


def get_settings_path(bitprecise, settings_search_string):
    if bitprecise:
        print("Using bit-precise analysis")
        settings_search_string = settings_search_string + "*_" + "Bitvector"
    else:
        print("Using default analysis")
        settings_search_string = settings_search_string + "*_" + "Default"

    settings_argument = search_config_dir("*" + settings_search_string + "*.epf")

    if settings_argument == "" or settings_argument is None:
        print("No suitable settings file found using " + settings_search_string)
        print("ERROR: UNSUPPORTED PROPERTY")
        raise _AbortButPrint("ERROR: UNSUPPORTED PROPERTY")
    return settings_argument


def check_file(f):
    if not os.path.isfile(f):
        raise argparse.ArgumentTypeError("File %s does not exist" % f)
    return f


def check_dir(d):
    if not os.path.isdir(d):
        raise argparse.ArgumentTypeError("Directory %s does not exist" % d)
    return d


def check_witness_type(witness, type):
    tree = elementtree.parse(witness)
    namespace = "{http://graphml.graphdrawing.org/xmlns}"
    query = ".//{0}graph/{0}data[@key='witness-type']".format(namespace)
    elem = tree.find(query)
    if elem is not None:
        if type == elem.text:
            return
        else:
            print(
                'Provided witness file has type "{}", but you specified witness type "{}"'.format(
                    elem.text, type
                )
            )
    else:
        print(
            'Could not find node with xpath query "{}" in witness file "{}", XML malformed?'.format(
                query, witness
            )
        )
    sys.exit(ExitCode.FAIL_WRONG_WITNESS_TYPE)


def debug_environment():
    # first, list all environment variables
    print("--- Environment variables ---")
    for env in os.environ:
        print(str(env) + "=" + str(os.environ.get(env)))

    print("--- Machine ---")
    print(platform.uname())
    call_relaxed_and_print(["uname", "-a"])
    call_relaxed_and_print(["cat", "/proc/cpuinfo"])
    call_relaxed_and_print(["cat", "/proc/meminfo"])

    print("--- libs ---")
    call_relaxed_and_print(["ldconfig", "-p"])

    print("--- Java ---")
    java_bin = get_java()
    print("Using java binary {}".format(java_bin))
    call_relaxed_and_print([java_bin, "-version"])

    print("--- Files ---")
    file_counter = 0
    dir_counter = 0
    for root, dirs, files in os.walk(ultimatedir):
        for a_dir in dirs:
            absdir = os.path.join(root, a_dir)
            rights = oct(os.stat(absdir)[ST_MODE])[-3:]
            print(str(rights) + " D " + str(absdir))
            dir_counter = dir_counter + 1
        for a_file in files:
            absfile = os.path.join(root, a_file)
            rights = oct(os.stat(absfile)[ST_MODE])[-3:]
            print(str(rights) + " F " + str(absfile))
            file_counter = file_counter + 1
    print(str(file_counter) + " files total, " + str(dir_counter) + " dirs total")

    print("--- Versions ---")
    print(version)
    call_relaxed_and_print(create_callargs(create_ultimate_base_call(), ["--version"]))
    solver_versions = [
        ("z3", "-version"),
        ("mathsat", "-version"),
        ("cvc4", "--version"),
        ("cvc4nyu", "--version"),
    ]
    for solver, vflag in solver_versions:
        abs_solver = os.path.join(ultimatedir, solver)
        call_relaxed_and_print([abs_solver, vflag])
        call_relaxed_and_print(["sha256sum", abs_solver])

    print("--- umask ---")
    call_relaxed_and_print(["touch", "testfile"])
    call_relaxed_and_print(["ls", "-al", "testfile"])
    call_relaxed_and_print(["rm", "testfile"])


def call_relaxed_and_print(call_args):
    if call_args is None:
        print("No call_args given")
    try:
        child_process = subprocess.Popen(
            call_args,
            stdout=subprocess.PIPE,
            preexec_fn=None if is_windows() else _init_child_process,
        )
        stdout, stderr = child_process.communicate()
    except Exception as ex:
        print("Error trying to start " + str(call_args))
        print(str(ex))
        return

    if stdout:
        print(stdout.decode("utf-8", "ignore"))
    if stderr:
        print("sdterr:")
        print(stderr.decode("utf-8", "ignore"))


def parse_args():
    # parse command line arguments
    global configdir
    global datadir
    global witnessdir
    global witnessname
    global enable_assertions

    parser = argparse.ArgumentParser(description="Ultimate wrapper script for SVCOMP")
    parser.add_argument(
        "--version", action="store_true", help="Print Ultimate.py's version and exit"
    )
    parser.add_argument(
        "--ultversion", action="store_true", help="Print Ultimate's version and exit"
    )
    parser.add_argument(
        "--config",
        nargs=1,
        metavar="<dir>",
        type=check_dir,
        help="Specify the directory in which the static config files are located; default is config/ "
        "relative to the location of this script",
    )
    parser.add_argument(
        "--data",
        nargs=1,
        metavar="<dir>",
        type=check_dir,
        help="Specify the directory in which the RCP config files are located; default is data/ "
        "relative to the location of this script",
    )
    parser.add_argument(
        "-ea", "--enable-assertions", action="store_true", help="Enable Java assertions"
    )
    parser.add_argument(
        "--full-output",
        action="store_true",
        help="Print Ultimate's full output to stderr after verification ends",
    )
    parser.add_argument(
        "--envdebug",
        action="store_true",
        help="Before doing anything, print as much information about the environment as possible",
    )
    parser.add_argument(
        "--spec",
        metavar="<file>",
        nargs=1,
        type=check_file,
        help="An property (.prp) file from SVCOMP",
    )
    parser.add_argument(
        "--architecture",
        choices=["32bit", "64bit"],
        help="Choose which architecture (defined as per SV-COMP rules) should be assumed",
    )
    parser.add_argument(
        "--file", metavar="<file>", nargs=1, type=check_file, help="One C file"
    )
    parser.add_argument(
        "--validate",
        nargs=1,
        metavar="<file>",
        type=check_file,
        help="Activate witness validation mode (if supported) and specify a .graphml file as witness",
    )
    parser.add_argument(
        "--witness-type",
        choices=["correctness_witness", "violation_witness"],
        help="Specify the type of witness you want to validate",
    )
    parser.add_argument(
        "--witness-dir",
        nargs=1,
        metavar="<dir>",
        type=check_dir,
        help="Specify the directory in which witness files should be saved; default is besides "
        "the script",
    )
    parser.add_argument(
        "--witness-name",
        nargs=1,
        help="Specify a filename for the generated witness; default is witness.graphml",
    )

    args, extras = parser.parse_known_args()

    if args.enable_assertions:
        enable_assertions = True

    if args.envdebug:
        debug_environment()
        sys.exit(ExitCode.SUCCESS)

    if args.version:
        print(version)
        sys.exit(ExitCode.SUCCESS)

    if args.ultversion:
        call_relaxed_and_print(create_ultimate_base_call() + ["--version"])
        sys.exit(ExitCode.SUCCESS)

    if args.file is None:
        print_err("--file is required")
        sys.exit(ExitCode.FAIL_NO_INPUT_FILE)

    if args.spec is None:
        print_err("--spec is required")
        sys.exit(ExitCode.FAIL_NO_SPEC)

    if args.architecture is None:
        print_err("--architecture is required")
        sys.exit(ExitCode.FAIL_NO_ARCH)

    witness = None
    c_file = args.file[0]
    property_file = args.spec[0]

    if args.validate:
        witness = args.validate[0]
        if args.witness_type:
            check_witness_type(witness, args.witness_type)

    if args.config:
        configdir = args.config[0]

    if args.witness_dir:
        witnessdir = args.witness_dir[0]

    if args.witness_name:
        witnessname = args.witness_name[0]

    if args.data:
        print("Setting data dir to {0}".format(args.data[0]))
        datadir = args.data[0]

    if c_file is None and witness is not None:
        print_err("You did not specify a C file with your witness")
        sys.exit(ExitCode.FAIL_NO_INPUT_FILE)

    if not args.validate and witness is not None:
        print_err("You did specify a witness but not --validate")
        sys.exit(ExitCode.FAIL_MULTIPLE_FILES)

    if args.validate and witness is None:
        print_err("You did specify --validate but no witness")
        sys.exit(ExitCode.FAIL_NO_WITNESS_TO_VALIDATE)

    if args.validate:
        return (
            property_file,
            args.architecture,
            [args.file[0], witness],
            args.full_output,
            args.validate,
            extras,
        )
    else:
        return (
            property_file,
            args.architecture,
            [args.file[0]],
            args.full_output,
            args.validate,
            extras,
        )


def create_settings_search_string(prop, architecture):
    if prop.is_mem_deref_memtrack():
        print("Checking for memory safety (deref-memtrack)")
        settings_search_string = "DerefFreeMemtrack"
    elif prop.is_only_mem_deref():
        print("Checking for memory safety (deref)")
        settings_search_string = "Deref"
    elif prop.is_mem_cleanup():
        print("Checking for memory safety (memcleanup)")
        settings_search_string = "MemCleanup"
    elif prop.is_termination():
        print("Checking for termination")
        settings_search_string = "Termination"
    elif prop.is_overflow():
        print("Checking for overflows")
        settings_search_string = "Overflow"
    elif prop.is_ltl():
        print("Checking for LTL property {0}".format(prop.get_ltl_formula()))
        settings_search_string = "LTL"
    elif prop.is_data_race():
        print("Checking for data races")
        settings_search_string = "DataRace"
    else:
        print("Checking for ERROR reachability")
        settings_search_string = "Reach"
    settings_search_string = settings_search_string + "*" + architecture
    return settings_search_string


def get_toolchain_path(prop, witnessmode):
    if prop.is_termination():
        if witnessmode:
            search_string = "*TerminationWitnessValidation.xml"
        else:
            search_string = "*Termination.xml"
    elif witnessmode:
        search_string = "*ReachWitnessValidation.xml"
    elif prop.is_any_mem():
        search_string = "*MemDerefMemtrack.xml"
    elif prop.is_ltl():
        search_string = "*LTL.xml"
    else:
        search_string = "*Reach.xml"

    toolchain = search_config_dir(search_string)

    if toolchain == "" or toolchain is None:
        print("No suitable toolchain file found using " + search_string)
        sys.exit(ExitCode.FAIL_NO_TOOLCHAIN_FOUND)

    return toolchain


def add_ltl_file_if_necessary(prop, input_files):
    if not prop.is_ltl():
        return input_files

    ltl_file = write_ltl(prop.get_ltl_formula())
    return input_files + [ltl_file]


def print_err(*objs):
    print(*objs, file=sys.stderr)


def main():
    # before doing anything, set permissions
    # call_relaxed(['chmod', 'ug+rwx', '-R', ultimatedir])

    (
        property_file,
        architecture,
        input_files,
        verbose,
        validate_witness,
        extras,
    ) = parse_args()
    prop = _PropParser(property_file)

    toolchain_file = get_toolchain_path(prop, validate_witness)
    settings_search_string = create_settings_search_string(prop, architecture)
    try:
        settings_file = get_settings_path(False, settings_search_string)
    except _AbortButPrint:
        # just abort, there is nothing to print left
        sys.exit(ExitCode.FAIL_NO_SETTINGS_FILE_FOUND)

    # create manual settings that override settings files for witness passthrough (collecting various things)
    # and for witness validation
    cli_arguments = create_cli_settings(
        prop, validate_witness, architecture, input_files
    )
    if not validate_witness:
        input_files = add_ltl_file_if_necessary(prop, input_files)

    # execute ultimate
    print("Version " + version)
    ultimate_bin = create_ultimate_base_call()
    ultimate_call = create_callargs(
        ultimate_bin,
        ["-tc", toolchain_file, "-i", input_files, "-s", settings_file, cli_arguments],
    )
    if extras:
        ultimate_call = ultimate_call + extras

    # actually run Ultimate, first in integer mode
    result, result_msg, overapprox, ultimate_output, error_path = run_ultimate(
        ultimate_call, prop, verbose
    )

    if overapprox or result.startswith("ERROR") or result.startswith("UNKNOWN"):
        try:
            settings_file = get_settings_path(True, settings_search_string)
        except _AbortButPrint:
            # there is no settings file for a bit-precise run
            pass
        else:
            # we did fail because we had to overapproximate. Lets rerun with bit-precision
            print("Retrying with bit-precise analysis")
            ultimate_call = create_callargs(
                ultimate_bin,
                [
                    "-tc",
                    toolchain_file,
                    "-i",
                    input_files,
                    "-s",
                    settings_file,
                    cli_arguments,
                ],
            )
            if extras:
                ultimate_call = ultimate_call + extras

            bit_precise_marker = "### Bit-precise run ###"
            if verbose:
                print()
                print(bit_precise_marker)

            (
                result,
                result_msg,
                overapprox,
                ultimate_bitprecise_output,
                error_path,
            ) = run_ultimate(ultimate_call, prop, verbose)
            ultimate_output = (
                ultimate_output
                + f"\n{bit_precise_marker}\n"
                + ultimate_bitprecise_output
            )

    # summarize results
    if write_ultimate_output_to_file:
        print("Writing output log to file {}".format(output_file_name))
        output_file = open(output_file_name, "wb")
        output_file.write(ultimate_output.encode("utf-8"))

    if result.startswith("FALSE"):
        print(
            "Writing human readable error path to file {}".format(error_path_file_name)
        )
        err_output_file = open(error_path_file_name, "wb")
        err_output_file.write(error_path.encode("utf-8"))
        if not prop.is_reach() and not prop.is_data_race():
            result = "FALSE({})".format(result_msg)

    print("Result:")
    print(result)
    sys.exit(
        ExitCode.FAIL_ULTIMATE_ERROR if result.startswith("ERROR") else ExitCode.SUCCESS
    )


def is_windows():
    return sys.platform == "win32"


def signal_handler(sig, frame):
    print("Killed by {}".format(sig))
    sys.exit(ExitCode.FAIL_SIGNAL)


if __name__ == "__main__":
    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)
    # just ignore pipe exceptions
    if not is_windows():
        signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    main()
