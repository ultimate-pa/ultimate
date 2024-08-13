#!/usr/bin/python3

import argparse
import os
import shutil
import subprocess

from webinterface.build_all_settings import build_all_settings
from webinterface.copy_examples import clean_examples, copy_examples
from webinterface.refresh_index import refresh_index


SCRIPT_DIR            = os.path.dirname(__file__)
PRODUCTION_CONFIG_DIR = os.path.join(SCRIPT_DIR, '..', '..', '..', '..', 'releaseScripts', 'website-config', 'frontend')


def parse_args() -> argparse.Namespace:
    try:
        parser = argparse.ArgumentParser(description="Build static website.")
        parser.add_argument(
            "--production",
            action="store_true",
            help="build site for deployment"
        )
        return parser.parse_args()
    except argparse.ArgumentError as exc:
        print(exc.message + "\n" + exc.argument)
        sys.exit(1)


def run_jekyll(production_build=False):
    subprocess.run(["bundle", "exec", "jekyll", "clean"], check=True)

    baseurl_params = ["--baseurl", "/"] if production_build else []
    subprocess.run(["bundle", "exec", "jekyll", "build", *baseurl_params], check=True)


def copy_webinterface_config(production_build):
    tgt = os.path.join(SCRIPT_DIR, '..', '_site', 'js', 'webinterface', 'config.js')
    if production_build:
        print("Copying webinterface config for production build")
        src = os.path.join(PRODUCTION_CONFIG_DIR, 'config.js')
        shutil.copyfile(src, tgt)
    elif not os.path.isfile(tgt):
        print("Copying default webinterface config")
        src = os.path.join(SCRIPT_DIR, '..', 'js', 'webinterface', 'config.dist.js')
        shutil.copyfile(src, tgt)


def build(production_build=False):
    # create settings JSON for webinterface
    build_all_settings()

    # copy and index examples for webinterface
    clean_examples()
    copy_examples()
    refresh_index()

    # build the static jekyll site
    run_jekyll(production_build)

    # copy the appropriate webinterface settings to _site/
    copy_webinterface_config(production_build)


if __name__ == '__main__':
    args = parse_args()
    build(args.production)

