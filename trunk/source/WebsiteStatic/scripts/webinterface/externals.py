#!/usr/bin/python3
# Provides helper functions for calling external utilities and checking, wether they are available.

from functools import cache
from pathlib import Path
import shutil
import subprocess


@cache
def get_ultimate_cli() -> list[str]:
    ult_bin = shutil.which("Ultimate")
    if not ult_bin:
        raise ValueError("Ultimate binary not found in PATH")
    ult_bin = Path(ult_bin)
    jar = (
        ult_bin.parent
        / "plugins"
        / "org.eclipse.equinox.launcher_1.7.100.v20251111-0406.jar"
    )
    datadir = ult_bin.parent / "data"
    return [
        "java",
        "-jar",
        jar,
        "-data",
        "@noDefault",
        "-ultimatedata",
        datadir,
    ]


@cache
def get_bundle_cli() -> list[str]:
    bin = shutil.which("bundle")
    if not bin:
        raise ValueError("'bundle' binary not found in PATH")
    return [bin]

def ensure_bundle_install():
    subprocess.run(get_bundle_cli() + ["install"], check=True)

@cache
def get_jekyll_cli() -> list[str]:
    jekyll = get_bundle_cli() + ["exec", "jekyll"]
    subprocess.run(jekyll + ["--version"], stdout=subprocess.DEVNULL, check=True)
    return jekyll
