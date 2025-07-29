#!/usr/bin/python3

import argparse
import os
import shutil
import subprocess
import sys


from webinterface.build_all_settings import build_all_settings
from webinterface.copy_examples import clean_examples, copy_examples
from webinterface.refresh_index import refresh_index
from webinterface.externals import get_jekyll_cli, get_ultimate_cli, ensure_bundle_install


SCRIPT_DIR = os.path.dirname(__file__)
PRODUCTION_CONFIG_DIR = os.path.join(
    SCRIPT_DIR, "..", "..", "..", "..", "releaseScripts", "website-config", "frontend"
)


def parse_args() -> argparse.Namespace:
    try:
        parser = argparse.ArgumentParser(description="Build static website.")
        parser.add_argument(
            "--production", action="store_true", help="build site for deployment"
        )
        parser.add_argument(
            "--skip-settings", action="store_true", help="skip rebuilding settings (useful during debugging)"
        )
        parser.add_argument(
            "--baseurl", action="store", type=str, help="set base URL for site (necessary when hosting the site in a sub-directory)"
        )
        return parser.parse_args()
    except argparse.ArgumentError as exc:
        print(exc.message + "\n" + exc.argument)
        sys.exit(1)


def run_jekyll(production_build=False, baseurl=None):
    subprocess.run(get_jekyll_cli() + ["clean"], check=True)
    baseurl_params = []

    if production_build:
        baseurl_params = ["--baseurl", "/"]
    elif baseurl is not None:
        baseurl_params = ["--baseurl", baseurl]

    subprocess.run(get_jekyll_cli() + ["build", *baseurl_params], check=True)


def copy_webinterface_config(production_build):
    tgt = os.path.join(SCRIPT_DIR, "..", "_site", "js", "webinterface", "config.js")
    if production_build:
        print("Copying webinterface config for production build")
        src = os.path.join(PRODUCTION_CONFIG_DIR, "config.js")
        shutil.copyfile(src, tgt)
    elif not os.path.isfile(tgt):
        print("Copying default webinterface config")
        src = os.path.join(SCRIPT_DIR, "..", "js", "webinterface", "config.dist.js")
        shutil.copyfile(src, tgt)


def build(production_build=False, skip_settings=False, baseurl=None):
    # check if external tools are available
    if not skip_settings:
        get_ultimate_cli()
    ensure_bundle_install()
    get_jekyll_cli()

    # create settings JSON for webinterface
    if not skip_settings:
        build_all_settings()

    # copy and index examples for webinterface
    clean_examples()
    copy_examples()
    refresh_index()

    # build the static jekyll site
    run_jekyll(production_build, baseurl)

    # copy the appropriate webinterface settings to _site/
    copy_webinterface_config(production_build)


if __name__ == "__main__":
    args = parse_args()
    build(args.production, args.skip_settings, args.baseurl)
