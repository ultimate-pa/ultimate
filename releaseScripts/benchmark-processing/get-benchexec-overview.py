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
from enum import Enum
from functools import lru_cache
from pathlib import Path
from typing import (
    Tuple,
    List,
    Iterator,
    Any,
    Dict,
    Optional,
    Pattern,
    ChainMap,
    TypeVar,
)

import mmap
import math
import contextlib
import yaml
from tqdm import tqdm

# some type defs
# first is category, second is message
Classification = Tuple[str, str]
T = TypeVar("T", bound=Any)


class InterestingSets(Enum):
    disabled = "Disabled"
    smt_comp = "SMT-COMP"


class EnumAction(argparse.Action):
    """
    Argparse action for handling Enums
    """

    def __init__(self, **kwargs):
        enum_type = kwargs.pop("type", None)
        if enum_type is None:
            raise ValueError("type must be assigned an Enum when using EnumAction")
        if not issubclass(enum_type, Enum):
            raise TypeError("type must be an Enum when using EnumAction")

        kwargs.setdefault("choices", tuple(e.value for e in enum_type))
        super(EnumAction, self).__init__(**kwargs)
        self._enum = enum_type

    def __call__(self, parser, namespace, values, option_string=None):
        value = self._enum(values)
        setattr(namespace, self.dest, value)


class UnsupportedLogFile(ValueError):
    """
    Raised when the log file is not an Ultimate log file
    """

    pass


class Result:
    version: str
    call: str
    classification: Classification
    logfile: str

    def __init__(
        self,
        logfile: Optional[str],
        result: Optional[Classification],
        call: Optional[str],
        version: Optional[str],
    ) -> None:
        self.logfile = logfile
        self.version = version
        self.call = call
        self.classification = result

    def __str__(self) -> str:
        return str(self.classification)

    def category(self) -> str:
        return self.classification[0]

    def message(self) -> str:
        return self.classification[1]

    @lru_cache(maxsize=1)
    def input_file(self) -> Optional[str]:
        if self.call is None:
            return None
        regex = r"-i\s+[\"]?(.*)[\"]?\s?"
        match = re.search(regex, self.call)
        if match is None:
            return None
        return match.group(1)


class Run:
    logfile_basename: str
    cputime: float
    walltime: float
    memory: int
    status: str
    category: str
    options: str
    properties: str
    name: str

    def __init__(self, xml_run: ET.Element, logfile_basename: str) -> None:
        self.logfile_basename = logfile_basename
        self.options = xml_run.attrib["options"] if "options" in xml_run.attrib else ""
        self.status = Run.__get_column_value(xml_run, "status")
        self.category = Run.__get_column_value(xml_run, "category")
        self.cputime = Run.__time_to_float(Run.__get_column_value(xml_run, "cputime"))
        self.walltime = Run.__time_to_float(Run.__get_column_value(xml_run, "walltime"))
        self.memory = Run.__byte_to_int(Run.__get_column_value(xml_run, "memory"))
        self.properties = (
            xml_run.attrib["properties"] if "properties" in xml_run.attrib else ""
        )
        self.name = xml_run.attrib.get("name", "")

    def is_timeout(self) -> bool:
        return self.status == "TIMEOUT"

    def is_oom(self) -> bool:
        return self.status == "OUT OF MEMORY"

    def is_unsound(self) -> bool:
        return self.category == "wrong"

    @staticmethod
    def __get_column_value(xml_run: ET.Element, title: str) -> Optional[str]:
        column = xml_run.find(f"./column[@title='{title}']")
        if column is None:
            return None
        return column.attrib["value"]

    @staticmethod
    def __time_to_float(val: str) -> float:
        """Remove second unit from benchexec time and convert to float"""
        num, unit = Run.split_number_and_unit(val)
        if not unit or unit == "s":
            return float(num) if val else None
        else:
            raise ValueError(f"unknown unit: {unit}")

    @staticmethod
    def __byte_to_int(val: str) -> int:
        """Remove byte unit from benchexec time and convert to float"""
        return int(val[:-1]) if val else None

    @staticmethod
    def split_number_and_unit(s: str) -> Tuple[str, str]:
        if not s:
            raise ValueError("empty value")
        s = s.strip()
        pos = len(s)
        while pos and not s[pos - 1].isdigit():
            pos -= 1
        number = s[:pos]
        unit = s[pos:].strip()
        return number, unit


class MessageClassifier:
    category: str
    message: str
    show_line: bool
    dump_smt: bool
    delta_debug: bool
    delta_debug_result_type: str
    delta_debug_short: bool
    delta_debug_category: bool

    def __init__(
        self, category: str, message: str, values: Dict[str, Any] = None
    ) -> None:
        self.category = category
        self.message = message
        self.show_line = True
        self.dump_smt = False
        self.delta_debug = False
        self.delta_debug_result_type = "ExceptionOrErrorResult"
        self.delta_debug_short = True
        self.delta_debug_category = True

        if values:
            self.show_line = values.get("show_line", self.show_line)
            self.dump_smt = values.get("dump_smt", self.dump_smt)
            self.delta_debug = values.get("delta_debug", self.delta_debug)
            self.delta_debug_result_type = values.get(
                "delta_debug_result_type", self.delta_debug_result_type
            )
            self.delta_debug_short = values.get(
                "delta_debug_short", self.delta_debug_short
            )
            self.delta_debug_category = values.get(
                "delta_debug_category", self.delta_debug_category
            )

    def __str__(self) -> str:
        return f"[{type(self).__name__}] {self.category}: {self.message} show_line={self.show_line} dump_smt={self.dump_smt} delta_debug={self.delta_debug}"


# global variables
order: List[Dict[str, MessageClassifier]] = []
interesting_strings: ChainMap[str, MessageClassifier] = collections.ChainMap()
str_no_result_unknown: str = "Unknown"
str_benchexec_timeout: str = "Timeout by benchexec"
str_benchexec_oom: str = "OOM by benchexec"
version_matcher: Pattern[str] = re.compile(r"^.*(\d+\.\d+\.\d+-\w+).*$")
enable_debug: bool = False
enable_trace: bool = False


def class_idx(result: Classification) -> int:
    if not result or not result[0]:
        return len(order) + 1
    return [i for i, e in enumerate(order) if result[0] in e][0]


def signal_handler(sig, frame) -> None:
    if sig == signal.SIGTERM:
        print("Killed by {}".format(sig))
    print("Abort by user: you pressed Ctrl+C!")
    sys.exit(2)


def limit(msg: str, lim: int) -> str:
    if lim < 4:
        raise ValueError("limit must be larger or equal 4 but was {}".format(lim))
    if len(msg) > lim:
        return msg[0 : lim - 3] + "..."
    return msg.ljust(lim, " ")


def n_min(items: List[T], n: int, key=lambda x: x) -> List[T]:
    if n >= len(items):
        mins = items
        mins.sort(key=key)
        return mins
    mins = items[:n]
    mins.sort(key=key)
    for i in items[n:]:
        if key(i) < key(mins[-1]):
            mins.append(i)
            mins.sort(key=key)
            mins = mins[:n]
    return mins


def is_file(value: str) -> str:
    if not os.path.isdir(value) and not os.path.isfile(value):
        raise argparse.ArgumentTypeError(f"{value} is not a directory")
    return value


def is_positive(value: str) -> int:
    as_int = int(value)
    if as_int <= 0:
        raise argparse.ArgumentTypeError(f"{value} is not a positive int value")
    return as_int


def format_number(number: float, number_of_digits: int) -> str:
    if number is None:
        return ""
    return f"{number:.{number_of_digits}f}"


def debug(msg: str) -> None:
    if enable_debug:
        print(msg)


def trace(msg: str) -> None:
    if enable_trace:
        print(msg)


def parse_args() -> argparse.Namespace:
    try:
        parser = argparse.ArgumentParser(
            description="Scan Ultimate log file(s) (and benchexec result XML files) for results types and print statistics for those."
        )
        parser.add_argument(
            "-i",
            "--input",
            metavar="<dir>",
            required=True,
            type=is_file,
            help="Specify directory containing Benchexec XML files, Ultimate log files, or a single log file.",
        )
        parser.add_argument(
            "--fastest-n",
            metavar="<n>",
            type=is_positive,
            default=1,
            help="Specify how many of the fastest examples per category should be shown."
            "Default: 1",
        )
        parser.add_argument(
            "--cut-off",
            metavar="<n>",
            type=is_positive,
            default=10,
            help="The size of the result class that should be grouped separately at the bottom."
            "Default: 10",
        )
        parser.add_argument(
            "--generate-interesting-set",
            type=InterestingSets,
            action=EnumAction,
            default=InterestingSets.disabled,
            help="Instead of generating overviews, generate a .set file from the input based on some heuristics.",
        )

        return parser.parse_args()
    except argparse.ArgumentError as exc:
        print(exc.message + "\n" + exc.argument)
        sys.exit(1)


def match_version(line: str):
    version_match = version_matcher.findall(line)
    if version_match:
        return version_match[0]
    return "Unknown"


def scan_line(
    line: str, result: Optional[Classification], line_iter: Iterator[str]
) -> Classification:
    new_result = None
    trace("Looking at line {}".format(line))

    for message, mc in interesting_strings.items():
        if message in line:
            if mc.show_line:
                new_result = message, line
            else:
                try:
                    new_result = message, line_iter.__next__()
                    debug("Found result {} with line {}".format(message, line))
                except StopIteration:
                    pass
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
    debug("Keeping old result because new one has lower priority")
    return result


def rescan_wrapper_preamble(file: str, call: str, version: str) -> List[Result]:
    """
    If there was no result in the wrapper script log so far, we rescan it and search for errors reported directly by
    the wrapper script
    """
    debug("Rescanning wrapper preamble")
    with open(file) as f:
        lines = [line.rstrip("\n") for line in f].__iter__()

        regex_file_does_not_exist = re.compile(".*File.*does not exist")
        classification = None
        for line in lines:
            if not line:
                continue
            if "Ultimate.py: error: argument" in line:
                debug("Found argument error")
                # hacky special case
                if "--validate" in line and regex_file_does_not_exist.match(line):
                    return [Result(file, scan_line(line, None, lines), None, None)]
                return [Result(file, None, None, None)]
            else:
                classification = scan_line(line, classification, lines)

        return [Result(file, classification, call, version)]
    # We just assume that the wrapper script was killed without any chance to print a message.
    # In this case we group the result as timeout and return a hardcoded line
    return [Result(file, ("Killed from outside", "..."), call, version)]


def process_wrapper_script_log(file: str) -> List[Result]:
    results: List[Result] = []
    default: bool = True
    wrapper_output: bool = True
    collect_call: bool = False
    version: Optional[str] = None
    classification: Optional[Classification] = None
    default_call: Optional[str] = None
    bitvec_call: Optional[str] = None
    with open(file) as f:
        lines = [line.rstrip("\n") for line in f].__iter__()
        for line in lines:
            if not line:
                continue
            if wrapper_output:
                if "### Bit-precise run ###" in line:
                    default = False
                elif line.startswith("Calling Ultimate with:"):
                    call: List[str] = [line]
                    collect_call = True
                elif "--- Real Ultimate output ---" in line:
                    wrapper_output = False
                    if collect_call:
                        collect_call = False
                        if default:
                            default_call = " ".join(call)
                            debug("Found default call {}".format(default_call))
                        else:
                            bitvec_call = " ".join(call)
                            debug("Found bitvector call {}".format(bitvec_call))
                elif collect_call:
                    call += [line]
            else:
                if line.startswith("This is Ultimate"):
                    new_version = match_version(line)
                    if version and not new_version == version:
                        raise ValueError(
                            "Found different Ultimate versions in one log file. First was {} and second was {}".format(
                                version, new_version
                            )
                        )
                    version = new_version
                    debug("Found Ultimate version {}".format(version))
                elif line.startswith("--- End real Ultimate output ---"):
                    if default:
                        debug(f"Final result for default mode: {classification}")
                        results += [Result(file, classification, default_call, version)]
                        classification = None
                        wrapper_output = True
                    else:
                        debug(f"Final result for bitvec mode: {classification}")
                        results += [Result(file, classification, bitvec_call, version)]
                        classification = None
                        wrapper_output = True
                else:
                    classification = scan_line(line, classification, lines)
    if classification is None and results:
        # Scanned wrapper log successfully
        debug(f"File {file} has {len(results)} results, run completed as expected")
        return results

    results += rescan_wrapper_preamble(
        file,
        default_call if default_call else (bitvec_call if bitvec_call else None),
        version,
    )
    if classification:
        # use last result we got from the Ultimate log as well
        results += [Result(file, classification, default_call, version)]

    debug(f"File {file} has {len(results)} results, run was interrupted")
    return results


def process_direct_call_log(file: str) -> List[Result]:
    result = None
    with open(file) as f:
        version = ""
        lines = [line.rstrip("\n") for line in f].__iter__()
        call = None
        for line in lines:
            if not line:
                continue
            if "/java " in line or line.startswith("java "):
                call = line
                debug("Found Ultimate call {}".format(call))
            elif line.startswith("This is Ultimate"):
                version = match_version(line)
                debug("Found Ultimate version {}".format(version))
            else:
                result = scan_line(line, result, lines)
        if call is None:
            print(file + " has no call")
        return [Result(file, result, call, version)]


def process_log_file(file: str) -> List[Result]:
    with open(file) as f:
        lines = [line.rstrip("\n") for line in f]
        for line in lines:
            if "Ultimate.py" in line:
                debug(f"Wrapper script detected for {file}")
                return process_wrapper_script_log(file)
            elif "This is Ultimate" in line:
                debug(f"No wrapper script detected for {file}")
                return process_direct_call_log(file)
    raise UnsupportedLogFile(
        "Encountered unrecognized file (not an Ultimate log file): {}".format(file)
    )


def print_results(
    results: List[Result], runs: Optional[Dict[str, Run]], args: argparse.Namespace
) -> None:
    cat_cnt = collections.Counter()
    result_cnt = collections.Counter()
    processed = {}
    for r in results:
        cat_cnt[r.category()] += 1
        if (
            r.category() == str_no_result_unknown
            or not interesting_strings[r.category()].show_line
        ):
            key = r.message()
        else:
            key = r.category()
        result_cnt[key] += 1
        processed[key] = r

    print("Categories")
    for cat, i in cat_cnt.most_common():
        print("{:>7}  {}".format(i, cat))
    print()

    print(f"Actual results (n>={args.cut_off})")
    print_cutoff = []
    print_detail = []
    print_cutoff_detail = []
    for subcat, j in result_cnt.most_common():
        r = processed[subcat]
        msg = "{:>7}  {}  {}:".format(j, limit(r.category(), 20), r.message())
        msg_detail = msg

        if runs:
            fastest = n_min(
                [
                    x
                    for x in results
                    if x.category() == r.category()
                    and x.message() == r.message()
                    and os.path.basename(x.logfile) in runs
                ],
                args.fastest_n,
                key=lambda y: runs[os.path.basename(y.logfile)].walltime,
            )
            for f in fastest:
                run = runs[os.path.basename(f.logfile)]
                msg_detail += (
                    f'\n{" ":<8} {format_number(run.walltime, 2):>8}s {f.logfile}'
                )
                msg_detail += f'\n{" ":<18} {"Call:":<8} {f.call}'
                if r.category() not in interesting_strings:
                    print(f"{r.category()} not in interesting_strings")
                    continue
                mc = interesting_strings[r.category()]
                if mc.delta_debug:
                    desc = (
                        "--deltadebugger.result.short.description.prefix"
                        if mc.delta_debug_short
                        else "--deltadebugger.result.long.description.prefix"
                    )
                    msg_detail += (
                        f'\n{" ":<18} {"Delta:":<8} {f.call} '
                        f'--deltadebugger.look.for.result.of.type "{mc.delta_debug_result_type}" '
                        f'{desc} "{r.category() if mc.delta_debug_category else r.message()}" '
                    )

                if mc.dump_smt:
                    dump_dir = Path(f"{os.path.dirname(f.logfile)}-dump")
                    dump_dir.mkdir(parents=True, exist_ok=True)
                    msg_detail += (
                        f'\n{" ":<18} {"Dump SMT:":<8} {f.call} '
                        f"--rcfgbuilder.dump.smt.script.to.file true "
                        f"--rcfgbuilder.compress.dumped.smt.script true "
                        f'--rcfgbuilder.to.the.following.directory "{dump_dir}" '
                        f"--traceabstraction.dump.smt.script.to.file true "
                        f"--traceabstraction.compress.dumped.smt.script true "
                        f'--traceabstraction.to.the.following.directory "{dump_dir}" '
                    )

        if j < args.cut_off:
            print_cutoff += [msg]
            print_cutoff_detail += [msg_detail]
        else:
            print(msg)
            print_detail += [msg_detail]

    if print_cutoff:
        print()
        print(f"Actual results (n<{args.cut_off})")
        for msg_detail in sorted(print_cutoff, reverse=True):
            print(msg_detail)

    if runs:
        print()
        print(f"Detailed actual results (n>={args.cut_off})")
        for msg in print_detail:
            print(msg)

        if print_cutoff_detail:
            print()
            print(f"Detailed actual results (n<{args.cut_off})")
            for msg_detail in sorted(print_cutoff_detail, reverse=True):
                print(msg_detail)


def set_unknowns(
    results: List[Result], file: str, runs: Dict[str, Run]
) -> List[Result]:
    real_results = []
    for r in results:
        if r.classification is None:
            basename = ntpath.basename(file)
            run = runs.get(basename, None)
            if not run:
                raise UnsupportedLogFile(f"There is no run for {file}")
            if run.is_timeout():
                real_results += [
                    Result(file, (str_benchexec_timeout, "..."), r.call, r.version)
                ]
            elif run.is_oom():
                real_results += [
                    Result(file, (str_benchexec_oom, "..."), r.call, r.version)
                ]
            else:
                real_results += [
                    Result(file, (str_no_result_unknown, file), r.call, r.version)
                ]
        else:
            real_results += [r]
    return real_results


def list_logfile_paths_in_dir(input_dir: str) -> Iterator[str]:
    for dirpath, dirnames, files in os.walk(input_dir):
        for file in files:
            if not file.endswith(".log"):
                continue
            yield os.path.join(dirpath, file)


def list_xml_filepaths(input_dir: str) -> Iterator[str]:
    for xml in os.listdir(input_dir):
        file = os.path.join(input_dir, xml)
        if os.path.isfile(file) and file.endswith(".xml"):
            yield file


def consume_task(
    queue: multiprocessing.Queue,
    results: List[Result],
    runs: Dict[str, Run],
    o: List[Dict[str, MessageClassifier]],
    i: ChainMap[str, MessageClassifier],
) -> None:
    global order
    global interesting_strings
    order = o
    interesting_strings = i
    tmp_result = []
    while True:
        path = queue.get()
        if path is None:
            break
        try:
            tmp_result += set_unknowns(process_log_file(path), path, runs)
        except UnsupportedLogFile:
            continue
    results += tmp_result


def process_input_dir(input_dir: str, runs: Dict[str, Run]) -> Tuple[int, List[Result]]:
    results: List[Result] = multiprocessing.Manager().list()
    if os.path.isfile(input_dir):
        results += set_unknowns(process_log_file(input_dir), input_dir, runs)
        log_file_count = 1
    else:
        local_cores = 1 if enable_debug else max(multiprocessing.cpu_count() - 4, 1)
        queue = multiprocessing.Queue(maxsize=local_cores)
        pool = multiprocessing.Pool(
            local_cores,
            initializer=consume_task,
            initargs=(queue, results, runs, order, interesting_strings),
        )

        progress_bar = tqdm([i for i in list_logfile_paths_in_dir(input_dir)])
        log_file_count = len(progress_bar)

        for path in progress_bar:
            progress_bar.set_description(
                "Processing ...{:100.100} [{:>3}C]".format(
                    path[len(input_dir) :], local_cores
                )
            )
            queue.put(path)

        # tell workers we're done
        for _ in range(local_cores):
            queue.put(None)
        pool.close()
        pool.join()
    # convert multiprocessing.Manager().list() to python list
    return log_file_count, [x for x in results]


def parse_benchexec_xmls(input_dir: str) -> Tuple[Dict[str, Run], bool]:
    xml_files = [f for f in list_xml_filepaths(input_dir)]
    if len(xml_files) == 0:
        print(
            "There are no benchexec .xml files in {}, cannot exclude timeouts properly".format(
                input_dir
            )
        )
        return {}, False

    rtr = {}
    pbar = tqdm(list(list_xml_filepaths(input_dir)))
    for xml in pbar:
        pbar.set_description(f"Parsing benchexec xml {xml[-100:]:100.100}")
        root = ET.parse(xml).getroot()
        result = root.find(".")
        name_attr = result.attrib.get("name", None)
        if not name_attr:
            print(
                f"Run in xml file {xml} has no name! Cannot detect toolname, ignoring .xml"
            )
            continue
        block_attr = result.attrib.get("block", None)
        if block_attr is not None and name_attr.endswith("." + block_attr):
            # Remove the suffix consisting of "." and the block
            tool_name = name_attr[: -len(block_attr) - 1]
        else:
            tool_name = name_attr
        for elem in root.findall(".//run"):
            # files = elem.attrib["files"]
            yml = elem.attrib["name"]
            base_yml = ntpath.basename(yml)
            logfile_basename = "{}.{}.log".format(tool_name, base_yml)
            try:
                rtr[logfile_basename] = Run(elem, logfile_basename)
            except ValueError as ve:
                print(f"Could not create Run from {logfile_basename}: {ve}")

    return rtr, True


def read_yaml_files() -> None:
    conf_file_name = "get-benchexec-overview.yaml"
    script_dir = os.path.dirname(os.path.realpath(__file__))

    with open(os.path.join(script_dir, conf_file_name)) as conf_file:
        conf = {}
        try:
            conf_yaml = yaml.safe_load(conf_file)
            for category, values in conf_yaml.items():
                conf[category] = {
                    k: MessageClassifier(category, k, v) for k, v in values.items()
                }

        except yaml.YAMLError as exc:
            print(f"Could not load configuration file {conf_file_name}: {exc}")
            sys.exit(1)

        global order
        global interesting_strings

        order = [
            conf["known_exceptions"],
            conf["known_timeouts"],
            {
                str_benchexec_timeout: MessageClassifier(
                    "known_timeouts", str_benchexec_timeout
                ),
                str_benchexec_oom: MessageClassifier(
                    "known_timeouts", str_benchexec_oom
                ),
            },
            conf["known_unsafe"],
            conf["known_unknown"],
            conf["known_safe"],
            conf["known_wrapper_errors"],
        ]

        interesting_strings = collections.ChainMap(*order)

        # todo: populate globals from conf


def main() -> None:
    args = parse_args()

    read_yaml_files()
    runs, benchexec_xml = parse_benchexec_xmls(args.input)

    # we should generate interesting sets, lets do that
    if args.generate_interesting_set != InterestingSets.disabled:
        if not benchexec_xml:
            print(
                f"{args.generate_interesting_set} requires benchexec XMLs, but there are none"
            )
            sys.exit(1)

        # get all logs with status timeout and property unreach-call
        interesting_runs = {
            k: v
            for k, v in runs.items()
            if v.is_timeout() and v.properties == "unreach-call"
        }

        # collect all that did not change to bitvector mode and did not die due to loop unrolling
        pbar = tqdm(list(list_logfile_paths_in_dir(args.input)))
        ymls = []

        regex_has_bv_run = re.compile(
            r"Retrying with bit-precise analysis".encode("utf-8")
        )
        regex_reached_trace_abstraction = re.compile(
            r"------------------------TraceAbstraction----------------------------".encode(
                "utf-8"
            )
        )
        regex_trace_histograms = re.compile(r"trace histogram \[(.*)\]".encode("utf-8"))
        for logfile in pbar:
            basename = ntpath.basename(logfile)
            pbar.set_description(f"Processing {basename[-100:]:100.100}")
            run = interesting_runs.get(basename, None)
            if not run:
                continue

            with open(logfile, "r", encoding="utf-8") as f:
                # open file memory mapped for performance reasons
                mm = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_COPY)
                with contextlib.closing(mm) as txt:
                    if regex_has_bv_run.search(txt):
                        continue
                    if not regex_reached_trace_abstraction.search(txt):
                        continue
                    trace_histograms = regex_trace_histograms.findall(txt)
                    if len(trace_histograms) > 3 and all(
                        int(h.split(",".encode("utf-8"))[0]) > 1
                        for h in trace_histograms[-3:]
                    ):
                        continue
                    ymls += [run.name]

        # print the ones that made it
        for yml in ymls:
            print(yml)

        return

    log_file_count, results = process_input_dir(args.input, runs)

    if log_file_count > len(results):
        if not benchexec_xml:
            msg = "missing benchexec files"
        else:
            msg = "something is wrong"
        print(
            "We processed {} .log files but collected only {} results. Possible reason: {}".format(
                log_file_count, len(results), msg
            )
        )
    else:
        len({k: v for k, v in runs.items() if v.is_timeout()})
        print(
            "Overview of {} results from {} .log files ({} {}, {} {})".format(
                len(results),
                log_file_count,
                len({k: v for k, v in runs.items() if v.is_timeout()}),
                str_benchexec_timeout,
                len({k: v for k, v in runs.items() if v.is_oom()}),
                str_benchexec_oom,
            )
        )
    print_results(results, runs, args)


if __name__ == "__main__":
    if sys.platform == "linux" or sys.platform == "linux2":
        signal.signal(signal.SIGINT, signal_handler)
        signal.signal(signal.SIGTERM, signal_handler)
        # just ignore pipe exceptions
        signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    main()
