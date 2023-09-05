#!/bin/python3

###############################################################################
#
# Builds JSON configuration for the Ultimate web interface from settings files
# (.epf) and, optionally, custom overrides for the web interface (.json).
#
# The overrides for the web interface are also used to indicate which settings
# should be visible in the UI (by default, all settings are invisible).
#
# When running this script, the Ultimate binary should be on the PATH.
#
###############################################################################

import os
import sys
import subprocess
import argparse
import json
import re

def is_file(value: str) -> str:
    if not os.path.isfile(value):
        raise argparse.ArgumentTypeError(f"{value} is not a file")
    return value

def parse_args() -> argparse.Namespace:
    try:
        parser = argparse.ArgumentParser(
            description="Construct JSON configuration for the ULTIMATE web interface."
        )
        parser.add_argument(
            "-s",
            "--settings",
            metavar="<settings>",
            required=True,
            type=is_file,
            help="Specify the .epf settings file used as basis for the configuration.",
        )
        parser.add_argument(
            "-tc",
            "--toolchain",
            metavar="<toolchain>",
            required=True,
            type=is_file,
            help="Specify the toolchain for which configuration shall be generated.",
        )
        parser.add_argument(
            "--override",
            metavar="<override>",
            type=is_file,
            default=None,
            help="A JSON file that overrides metadata for some configuration options. "
            "The file should contain an array of objects, each of which contains at least an 'id' key.",
        )

        return parser.parse_args()
    except argparse.ArgumentError as exc:
        print(exc.message + "\n" + exc.argument)
        sys.exit(1)


def get_ultimate_json(options):
    output = subprocess.check_output(['Ultimate', *options], stderr=subprocess.DEVNULL)
    
    # ignore ordinary log lines if they exist
    output = output.splitlines()[-1]
        
    return json.loads(output)['frontend_settings']


def get_overrides(path: str):
    if path is None:
        return []
    try:
        with open(path, 'r') as override_file:
            return json.load(override_file)
    except OSError as exc:
        print(exc.message)
        sys.exit(1)


def find_entry(entries, id: str):
    for i, entry in enumerate(entries):
        if entry['id'] == id:
            return i
    return -1

def main() -> None:
    args = parse_args()

    # Read default settings, delta given by epf file, and overrides for web interface
    defaults  = get_ultimate_json(['-tc', args.toolchain, '--generate-frontend-json-from-defaults'])
    delta     = get_ultimate_json(['-tc', args.toolchain, '-s', args.settings, '-i', 'dummy', '--generate-frontend-json-from-delta'])
    overrides = get_overrides(args.override)

    # Apply overrides to delta settings
    for entry in overrides:
        delta_index = find_entry(delta, entry['id'])
        if delta_index < 0:
            default_index = find_entry(defaults, entry['id'])
            if default_index < 0:
                print(f"ERROR: Could not find setting with ID {entry['id']}. Exiting...")
                sys.exit(1)
            default_entry = defaults[default_index]
            merged_entry = { **default_entry, **entry }
            delta.append(merged_entry)
        else:
            delta_entry = delta[delta_index]
            merged_entry = { **delta_entry, **entry }
            delta[delta_index] = merged_entry

    # Write delta settings
    print(json.dumps(delta, indent=2))


if __name__ == "__main__":
    main()


