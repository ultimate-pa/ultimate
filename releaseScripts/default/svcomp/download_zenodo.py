#!/usr/bin/env python3
import argparse
import logging
import os
import sys

import requests


def token_string_or_file(arg):
    if not os.path.exists(arg):
        return arg
    else:
        return open(arg, "r").read().strip()


logging.basicConfig(format="%(message)s", stream=sys.stdout)
logger = logging.getLogger(__package__)


def parse_args():
    parser = argparse.ArgumentParser(
        description="Upload latest Ultimate versions to Zenodo",
    )
    parser.add_argument(
        "--token",
        dest="token",
        metavar="<file> or <token>",
        default=None,
        type=token_string_or_file,
        required=True,
        help="The personal auth token for Zenodo. Default: None",
    )

    parser.add_argument(
        "--doi",
        dest="doi",
        metavar="<doi>",
        default=None,
        type=str,
        required=True,
        help="The DOI you want to download. Default: None",
    )

    args = parser.parse_args()

    token = os.environ.get(
        "ZENODO_PERSONAL_API_TOKEN", token_string_or_file(args.token)
    )
    os.environ["ZENODO_SANDBOX_API_TOKEN"] = token
    logger.setLevel(logging.INFO)
    args.token = token
    return args


args = parse_args()

if args.doi.startswith("10.5281/zenodo."):
    args.doi = args.doi.replace("10.5281/zenodo.", "")
else:
    print(f"Cannot download non-zenodo DOI {args.doi}")
    sys.exit(1)

params = {"access_token": args.token}
r = requests.get(f"https://zenodo.org/api/records/{args.doi}", params=params)
if not r:
    print(r)
    sys.exit(1)

download_urls = [f["links"]["self"] for f in r.json()["files"]]
filenames = [f["key"] for f in r.json()["files"]]
for filename, url in zip(filenames, download_urls):
    print("Downloading:", filename)
    r = requests.get(url, params=params)
    with open(filename, "wb") as f:
        f.write(r.content)
