#!/usr/bin/env python3
"""
Create a reduced BenchExec RunDefinition over SV-Benchmarks C tasks.

The script loops over all category set files (*.set) of the "c" folder of an
SV-Benchmarks checkout, resolves the globs in the set files to concrete task
(.yml) files, samples a given number of tasks per category (balanced between
expected-verdict true and false) and writes a single BenchExec benchmark XML
that lists the selected tasks explicitly instead of via <includesfile>.

Usage:
    python3 create_reduced_svcomp_benchmark_definition.py <sv-benchmarks-dir> \
                                                          <num-tasks> [options]
"""

import argparse
import glob
import random
import re
import sys
import xml.etree.ElementTree as ET
from pathlib import Path, PurePosixPath

try:
    import yaml
except ImportError:
    print("Error: PyYAML is required (pip install pyyaml)", file=sys.stderr)
    sys.exit(1)


# Fixed seed so that repeated runs produce the same reduced set.
RANDOM_SEED = 42

# Preferred order of the rundefinitions (properties not listed come last, sorted).
PROPERTY_ORDER = [
    "unreach-call",
    "no-overflow",
    "valid-memsafety",
    "valid-memcleanup",
    "no-data-race",
    "termination",
]

DEF_BEHAVIOR_PROPERTY = "def-behavior"


def positive_int(value):
    try:
        parsed = int(value)
    except ValueError:
        raise argparse.ArgumentTypeError(f"'{value}' is not an integer")
    if parsed <= 0:
        raise argparse.ArgumentTypeError(f"'{value}' must be a positive integer")
    return parsed


def positive_quantity(value):
    """Validate a BenchExec quantity like '15 min', '900' or '8GB'."""
    value = value.strip()
    if not value:
        raise argparse.ArgumentTypeError("value must not be empty")
    if not re.fullmatch(r"\d+(\.\d+)?\s*[a-zA-Z]*", value):
        raise argparse.ArgumentTypeError(
            f"'{value}' is not a positive quantity (e.g. '15 min', '900', '8GB')"
        )
    return value


def nonempty_string(value):
    if not value.strip():
        raise argparse.ArgumentTypeError("value must not be empty")
    return value


def parse_args():
    parser = argparse.ArgumentParser(
        description=(
            "Create a reduced BenchExec RunDefinition over SV-Benchmarks C tasks: "
            "samples a given number of tasks per category (set file) with a balanced "
            "split between expected-verdict true and false tasks."
        )
    )
    parser.add_argument(
        "sv_benchmarks_dir",
        type=Path,
        help="Path to an SV-Benchmarks checkout (must contain a 'c' folder)",
    )
    parser.add_argument(
        "num_tasks",
        type=positive_int,
        help="Number of tasks to select per category",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Path of the generated benchmark XML (default: print to stdout)",
    )
    parser.add_argument(
        "--path-prefix",
        type=nonempty_string,
        default="../sv-benchmarks/",
        help="Prefix prepended to the task/property paths relative to the generated XML "
        "(default: ../sv-benchmarks/)",
    )
    parser.add_argument(
        "--tool",
        type=nonempty_string,
        default="ultimateautomizer",
        help="Value of the 'tool' attribute of the benchmark element (default: ultimateautomizer)",
    )
    parser.add_argument(
        "--prefix-name",
        type=nonempty_string,
        default="SV-COMP27",
        help="Prefix of the rundefinition names (default: SV-COMP27)",
    )
    parser.add_argument(
        "--display-name",
        type=nonempty_string,
        default=None,
        help="Value of the 'displayName' attribute of the benchmark element (default: none)",
    )
    parser.add_argument(
        "--timelimit",
        type=positive_quantity,
        default="15 min",
        help="Value of the 'timelimit' attribute (default: 15 min)",
    )
    parser.add_argument(
        "--hardtimelimit",
        type=positive_quantity,
        default="16 min",
        help="Value of the 'hardtimelimit' attribute (default: 16 min)",
    )
    parser.add_argument(
        "--memlimit",
        type=positive_quantity,
        default="15 GB",
        help="Value of the 'memlimit' attribute (default: 15 GB)",
    )
    parser.add_argument(
        "--cpu-cores",
        type=positive_int,
        default=4,
        help="Value of the 'cpuCores' attribute (default: 4)",
    )
    args = parser.parse_args()

    if not args.sv_benchmarks_dir.is_dir():
        parser.error(f"SV-Benchmarks directory '{args.sv_benchmarks_dir}' does not exist")
    c_dir = args.sv_benchmarks_dir / "c"
    if not c_dir.is_dir():
        parser.error(f"SV-Benchmarks directory '{args.sv_benchmarks_dir}' does not contain a 'c' folder")
    if args.output is not None and args.output.exists() and args.output.is_dir():
        parser.error(f"Output path '{args.output}' is a directory")

    return args


def parse_set_file(set_file):
    """Parse a set file, returning the list of glob patterns (relative to the 'c' folder)."""
    patterns = []
    with open(set_file, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            patterns.append(line)
    return patterns


def resolve_patterns(c_dir, patterns, set_file):
    """Resolve the glob patterns of a set file to task (.yml) files relative to the 'c' folder."""
    tasks = set()
    for pattern in patterns:
        matches = sorted(glob.glob(str(c_dir / pattern)))
        if not matches:
            print(f"Warning: pattern '{pattern}' of {set_file.name} matches nothing", file=sys.stderr)
        for match in matches:
            path = Path(match)
            if path.is_dir():
                continue
            if path.suffix == ".c":
                # Old-style set files reference .c files; use the corresponding task .yml if present.
                yml = path.with_suffix(".yml")
                if yml.is_file():
                    path = yml
                else:
                    print(
                        f"Warning: skipping '{path.relative_to(c_dir)}' from {set_file.name}: "
                        "no corresponding .yml task file",
                        file=sys.stderr,
                    )
                    continue
            if path.suffix != ".yml":
                continue
            rel = path.relative_to(c_dir)
            if "witnesses" in rel.parts:
                # Skip witness validation tasks; they are not verification tasks.
                continue
            tasks.add(rel.as_posix())
    return sorted(tasks)


def normalize_property_name(prop_file, c_dir):
    """Map a property file to the name of the standard property it belongs to.

    Some tasks (e.g. ECA/RERS) declare per-task sub-properties like
    'unreach-call-0.prp' or 'unreach-call-a.prp'; these are mapped to the base
    property if the corresponding standard property file exists in the
    'c/properties' folder.
    """
    name = PurePosixPath(prop_file.replace("\\", "/")).name
    if name.endswith(".prp"):
        name = name[: -len(".prp")]
    if (c_dir / "properties" / f"{name}.prp").is_file():
        return name
    base = re.sub(r"-[A-Za-z0-9]+$", "", name)
    if base and base != name and (c_dir / "properties" / f"{base}.prp").is_file():
        return base
    return name


def parse_task_yml(c_dir, rel_path):
    """Parse a task .yml file, returning the properties as {property_name: expected_verdict}.

    Properties without an expected verdict are ignored. If a task declares
    several property files that map to the same property (e.g. the standard
    property plus RERS sub-properties), the verdict of the exact standard
    property file wins. Returns None if the file cannot be parsed.
    """
    try:
        with open(c_dir / rel_path, encoding="utf-8") as f:
            content = yaml.safe_load(f)
    except (OSError, yaml.YAMLError) as exc:
        print(f"Warning: cannot parse task '{rel_path}': {exc}", file=sys.stderr)
        return None
    if not isinstance(content, dict):
        return None
    entries = []
    for prop in content.get("properties") or []:
        if not isinstance(prop, dict):
            continue
        prop_file = prop.get("property_file")
        if not prop_file:
            continue
        prop_name = normalize_property_name(prop_file, c_dir)
        is_exact = PurePosixPath(prop_file.replace("\\", "/")).name == f"{prop_name}.prp"
        entries.append((is_exact, prop_name, prop.get("expected_verdict")))
    properties = {}
    for is_exact, prop_name, verdict in entries:
        if prop_name not in properties or (is_exact and not properties[prop_name][0]):
            properties[prop_name] = (is_exact, verdict)
    return {prop_name: verdict for prop_name, (_, verdict) in properties.items()}


def select_tasks(pool_true, pool_false, num_tasks):
    """Select num_tasks tasks balanced between true and false expected verdicts.

    Half of the tasks are sampled from each pool; if one pool is too small,
    the shortfall is filled from the other pool.
    """
    need_true = num_tasks // 2
    need_false = num_tasks - need_true
    selected_true = random.sample(pool_true, min(need_true, len(pool_true)))
    selected_false = random.sample(pool_false, min(need_false, len(pool_false)))
    remaining = num_tasks - len(selected_true) - len(selected_false)
    if remaining > 0:
        rest_true = [t for t in pool_true if t not in set(selected_true)]
        rest_false = [t for t in pool_false if t not in set(selected_false)]
        fill_true = random.sample(rest_true, min(remaining, len(rest_true)))
        remaining -= len(fill_true)
        fill_false = random.sample(rest_false, min(remaining, len(rest_false)))
        selected_true += fill_true
        selected_false += fill_false
    return sorted(selected_true), sorted(selected_false)


def build_benchmark(args, pools):
    benchmark = ET.Element("benchmark")
    benchmark.set("tool", args.tool)
    if args.display_name:
        benchmark.set("displayName", args.display_name)
    benchmark.set("timelimit", args.timelimit)
    benchmark.set("hardtimelimit", args.hardtimelimit)
    benchmark.set("memlimit", args.memlimit)
    benchmark.set("cpuCores", str(args.cpu_cores))

    def property_sort_key(prop):
        order = PROPERTY_ORDER.index(prop) if prop in PROPERTY_ORDER else len(PROPERTY_ORDER)
        return (order, prop)

    path_prefix = args.path_prefix.rstrip("/")
    for prop in sorted(pools, key=property_sort_key):
        rundefinition = ET.SubElement(benchmark, "rundefinition")
        rundefinition.set("name", f"{args.prefix_name}_{prop}")
        for stem in sorted(pools[prop]):
            tasks_elem = ET.SubElement(rundefinition, "tasks")
            tasks_elem.set("name", f"C.{prop}.{stem}")
            includes = pools[prop][stem][True] + pools[prop][stem][False]
            random.shuffle(includes)
            for rel_path in includes:
                include = ET.SubElement(tasks_elem, "include")
                include.text = f"{path_prefix}/c/{rel_path}"
            propertyfile = ET.SubElement(tasks_elem, "propertyfile")
            propertyfile.text = f"{path_prefix}/c/properties/{prop}.prp"
    return benchmark


def serialize_benchmark(benchmark):
    ET.indent(benchmark)
    xml_body = ET.tostring(benchmark, encoding="unicode")
    doctype = (
        '<!DOCTYPE benchmark PUBLIC "+//IDN sosy-lab.org//DTD BenchExec benchmark 2.3//EN" '
        '"https://www.sosy-lab.org/benchexec/benchmark-2.3.dtd">'
    )
    return f'<?xml version="1.0" encoding="UTF-8" standalone="yes"?>\n{doctype}\n{xml_body}\n'


def main():
    args = parse_args()
    random.seed(RANDOM_SEED)
    c_dir = args.sv_benchmarks_dir / "c"

    set_files = sorted(c_dir.glob("*.set"))
    if not set_files:
        print(f"Error: no .set files found in '{c_dir}'", file=sys.stderr)
        sys.exit(1)

    # pools[prop][stem][verdict] = list of task paths (relative to 'c')
    pools = {}
    for set_file in set_files:
        stem = set_file.name[: -len(".set")]
        patterns = parse_set_file(set_file)
        rel_tasks = resolve_patterns(c_dir, patterns, set_file)
        for rel_task in rel_tasks:
            properties = parse_task_yml(c_dir, rel_task)
            if properties is None:
                continue
            # Exclude invalid tasks: tasks whose def-behavior property is set to false.
            if properties.get(DEF_BEHAVIOR_PROPERTY) is False:
                continue
            for prop_name, verdict in properties.items():
                if verdict in (True, False) and prop_name != DEF_BEHAVIOR_PROPERTY:
                    pools.setdefault(prop_name, {}).setdefault(stem, {True: [], False: []})[verdict].append(rel_task)

    # Sample per (property, category) with a balanced split between true and false.
    total_selected = 0
    for prop, stems in pools.items():
        for stem in list(stems):
            pool_true, pool_false = stems[stem][True], stems[stem][False]
            selected_true, selected_false = select_tasks(pool_true, pool_false, args.num_tasks)
            if len(selected_true) + len(selected_false) < args.num_tasks:
                print(
                    f"Warning: C.{prop}.{stem} has only {len(pool_true)} true and {len(pool_false)} false "
                    f"tasks; selected {len(selected_true) + len(selected_false)} instead of {args.num_tasks}",
                    file=sys.stderr,
                )
            stems[stem] = {True: selected_true, False: selected_false}
            total_selected += len(selected_true) + len(selected_false)
            print(
                f"C.{prop}.{stem}: {len(pool_true)} true / {len(pool_false)} false tasks in pool, "
                f"selected {len(selected_true)} true / {len(selected_false)} false"
            )

    if not pools:
        print("Error: no tasks selected, nothing to write", file=sys.stderr)
        sys.exit(1)

    benchmark = build_benchmark(args, pools)
    xml = serialize_benchmark(benchmark)
    if args.output is not None:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(xml)
        print(f"Wrote {args.output} ({total_selected} tasks in {len(pools)} rundefinitions)")
    else:
        print(xml, end="")


if __name__ == "__main__":
    main()
