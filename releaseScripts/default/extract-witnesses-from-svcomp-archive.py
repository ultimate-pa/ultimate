#!/usr/bin/env python3

import hashlib
import logging
import os
import shutil
import traceback
from enum import Enum
from sys import exit
from argparse import ArgumentParser, BooleanOptionalAction
from logging import getLogger, INFO, DEBUG
from pathlib import Path
from json import load as json_safe_load
from yaml import safe_load as yaml_safe_load

logger = getLogger(__name__)


# ----------------------------------------------------------------------------------------------------------------------

class Property(Enum):
    NO_DATA_RACE = ("no-data-race", ["data-race"])
    NO_OVERFLOW = ("no-overflow", ["overflow"])
    TERMINATION = ("termination", ["end"])
    UNREACH_CALL = ("unreach-call", ["reach_error"])
    VALID_MEMCLEANUP = ("valid-memcleanup", ["valid-memcleanup"])
    VALID_MEMSAFETY = ("valid-memsafety", ["valid-free", "valid-deref", "valid-memtrack"])

    def __init__(self, svcomp_name: str, ltl_props: list[str]):
        self.svcomp_name = svcomp_name
        self.ltl_props = ltl_props

    def __str__(self):
        return self.svcomp_name

    @classmethod
    def from_string(cls, value: str):
        for prop in cls:
            if prop.svcomp_name == value:
                return prop
        raise ValueError(f"Unknown property: {value}")

    def matches_path(self, path: Path) -> bool:
        if self.svcomp_name in str(path):
            return True
        return False

    def matches_spec(self, spec: str) -> bool:
        for ltl_prop in self.ltl_props:
            if ltl_prop in spec:
                return True
        return False


class Format(Enum):
    GRAPHML = "graphml"
    YAML = "yml"

    def __init__(self, ext: str):
        self.ext = ext

    def __str__(self) -> str:
        return self.ext

    @classmethod
    def from_string(cls, value: str):
        for fmt in cls:
            if fmt.ext == value:
                return fmt
        raise ValueError(f"Unknown format: {value}")

    def matches_path(self, path: Path) -> bool:
        if path.suffix == f".{self.ext}":
            return True
        return False


# ----------------------------------------------------------------------------------------------------------------------

def benchmark_has_property(benchmark_def: dict, prop: Property) -> bool:
    """
    Check whether a benchmark definition contains the requested property.
    """
    benchmark_props = benchmark_def.get("properties", [])

    for benchmark_prop in benchmark_props:
        benchmark_prop_refs = Path(benchmark_prop.get("property_file", ""))
        if prop.matches_path(benchmark_prop_refs):
            return True

    return False


def benchmark_input_file(benchmark_def: dict, benchmark_def_path: Path) -> Path:
    """
    Return the referenced source file.
    """
    benchmark_inp_files = benchmark_def.get("input_files", [])

    if isinstance(benchmark_inp_files, list):
        assert len(benchmark_inp_files) == 1
        benchmark_inp_file = Path(benchmark_inp_files[0])
    else:
        benchmark_inp_file = Path(benchmark_inp_files)

    return (benchmark_def_path.parent / benchmark_inp_file).resolve()


def sha256_file(path: Path) -> str:
    """
    Compute the SHA256 hash of a file.
    """
    algo = hashlib.sha256()

    with path.open("rb") as file:
        while True:
            chunk = file.read(1024 * 1024)
            if not chunk:
                break
            algo.update(chunk)

    return algo.hexdigest()


def lookup_witness_files(witness_root: Path, witness_lookup: Path, output_root: Path, benchmark_def: Path,
                         input_src: Path, producer: str, prop: Property, fmt: Format) -> list[tuple[Path, Path]]:
    """
    Search for matching witnesses in lookup mapping.
    """
    witness_copy_table = []

    with witness_lookup.open("r", encoding="utf-8") as mappings_file:
        witness_mappings = json_safe_load(mappings_file)

        for witness_mapping in witness_mappings:
            # Check if producer tool matches referenced witness
            if not witness_mapping.get("producer", "").startswith(producer):
                continue

            # Check if specification matches referenced witness
            if not prop.matches_spec(witness_mapping.get("specification", "")):
                continue

            # Check if input file matches referenced witness
            input_src_name = input_src.name
            witness_prg_filename = Path(witness_mapping.get("programfile", "")).name
            if not input_src_name in str(witness_prg_filename):
                continue

            # Check if witness format matches referenced witness
            witness_src_path_rel = Path(witness_mapping.get("witness-file", ""))
            if not fmt.matches_path(witness_src_path_rel):
                continue

            # Compute witness filenames for extraction
            witness_src_path_abs = (witness_root / witness_src_path_rel).resolve()
            witness_dst_path_abs = (output_root / benchmark_def.name / f"witness.{fmt}").resolve()

            # Store copy filenames for extraction
            witness_copy_table.append((witness_src_path_abs, witness_dst_path_abs))

    return witness_copy_table


def copy_witness_files(copy_table: list[tuple[Path, Path]]):
    """
    Copy witnesses using copy table.
    """
    for witness_src_path, witness_dst_path in copy_table:
        logger.debug("Copy witness %s to output %s", witness_src_path, witness_dst_path)
        witness_dst_path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(witness_src_path, witness_dst_path)


def check_dir_exists_or_abort(path: Path) -> None:
    """
    Check if directory exists (and abort if not).
    """
    if not path.exists() or not path.is_dir():
        logger.error("Path '%s' is not an existing directory", path)
        exit(os.EX_OSFILE)


# ----------------------------------------------------------------------------------------------------------------------

def main():
    parser = ArgumentParser()

    parser.add_argument(
        "-d",
        "--debug",
        action=BooleanOptionalAction,
        help="Enable verbose logging",
    )

    parser.add_argument(
        "benchmark",
        type=Path,
        help="SV-COMP benchmark directory",
    )

    parser.add_argument(
        "archive",
        type=Path,
        help="SV-COMP witness archive directory",
    )

    parser.add_argument(
        "-p",
        "--property",
        required=True,
        type=Property.from_string,
        choices=list(Property),
        help="Property (e.g. unreach-call)",
    )

    parser.add_argument(
        "-f",
        "--format",
        required=True,
        type=Format.from_string,
        choices=list(Format),
        help="Witness format",
    )

    parser.add_argument(
        "-t",
        "--tool",
        required=True,
        help="Witness producer (e.g. Automizer, CPAchecker, etc.)",
    )

    parser.add_argument(
        "output",
        type=Path,
        help="SV-COMP witness output directory",
    )

    args = parser.parse_args()

    if args.debug:
        logging.basicConfig(level=DEBUG)
    else:
        logging.basicConfig(level=INFO)

    selected = 0
    copied = 0

    dir_witness_root = args.archive
    dir_witness_info = dir_witness_root / "witnessListByProgramHashJSON"
    check_dir_exists_or_abort(dir_witness_info)

    dir_benchmark_root = args.benchmark
    dir_benchmark_c = dir_benchmark_root / "c"
    check_dir_exists_or_abort(dir_benchmark_c)

    dir_output_root = args.output
    check_dir_exists_or_abort(dir_output_root)

    for benchmark_def_path in dir_benchmark_c.rglob("*.yml"):
        try:
            with benchmark_def_path.open("r", encoding="utf-8") as benchmark_def_file:
                benchmark_def = yaml_safe_load(benchmark_def_file)

                # Filter benchmark according to given property
                if not benchmark_has_property(benchmark_def, args.property):
                    logger.debug("Benchmark %s does not match property %s", benchmark_def_path, args.property)
                    continue

                selected += 1

                # Resolve source file of benchmark
                benchmark_inp_path = benchmark_input_file(benchmark_def, benchmark_def_path)
                if not benchmark_inp_path.exists():
                    logger.error("Missing input file %s in benchmark %s", benchmark_inp_path, benchmark_def_path)
                    continue

                # Compute source file hash
                benchmark_inp_hash = sha256_file(benchmark_inp_path)

                # Resolve witness lookup mapping file
                witness_inf_path = dir_witness_info / f"{benchmark_inp_hash}.json"
                if not witness_inf_path.exists():
                    logger.error("No witness found for input file %s", benchmark_inp_path)
                    continue

                logger.debug("%s", benchmark_inp_path)
                logger.debug("  SHA256 : %s", benchmark_inp_hash)
                logger.debug("  Lookup : %s", witness_inf_path)

                # Lookup witness files from lookup mapping
                copy_table = lookup_witness_files(dir_witness_root, witness_inf_path, dir_output_root,
                                                  benchmark_def_path, benchmark_inp_path, args.tool, args.property,
                                                  args.format)

                # Copy witness files to output directory
                copy_witness_files(copy_table)

                copied += len(copy_table)

        except Exception as e:
            logger.warning("%s: %s", benchmark_def_file, e)
            traceback.print_exc()

    logger.info("Benchmarks selected: %d", selected)
    logger.info("Witnesses copied   : %d", copied)


# ----------------------------------------------------------------------------------------------------------------------

if __name__ == "__main__":
    main()
