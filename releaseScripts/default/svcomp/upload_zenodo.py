#!/usr/bin/env python3
import argparse
import datetime
import logging
import os
from pathlib import Path
import re
import subprocess
import sys
import time
from typing import Union
import requests
from pprint import pformat, pprint
from requests import HTTPError
from zenodo_client import Creator, Metadata, Zenodo
from zenodo_client.api import Data, Paths
import pystow

# note
# tested the following API wrappers 1.11.2023:
# zenodo_client: extremely crappy, but seems like the best of the bunch
# zenodopy: does not allow creators
# pyzenodo3: couldnt figure out how to use it


def token_string_or_file(arg):
    if not os.path.exists(arg):
        return arg
    else:
        return open(arg, "r").read().strip()


ACCESS_TOKEN = None
logging.basicConfig(format="%(message)s", stream=sys.stdout)
logger = logging.getLogger(__package__)
logger.setLevel(logging.DEBUG)


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
        "--sandbox",
        dest="sandbox",
        default=True,
        type=bool,
        help="Should we use Zenodo's sandbox instead of the real Zenodo? Default: True",
    )
    args = parser.parse_args()

    ACCESS_TOKEN = os.environ.get(
        "ZENODO_PERSONAL_API_TOKEN", token_string_or_file(args.token)
    )
    os.environ["ZENODO_SANDBOX_API_TOKEN"] = ACCESS_TOKEN
    return args


def sizeof_fmt(num, suffix="B"):
    for unit in ("", "Ki", "Mi", "Gi", "Ti", "Pi", "Ei", "Zi"):
        if abs(num) < 1024.0:
            return f"{num:3.1f} {unit}{suffix}"
        num /= 1024.0
    return f"{num:.1f} Yi{suffix}"


def creator(
    name: str,
    affiliation: str = "University of Freiburg",
    orcid: str = None,
    gnd: str = None,
) -> Creator:
    return Creator(name=name, affiliation=affiliation, orcid=orcid, gnd=gnd)


def ensure(self: Zenodo, key: str, data: Data, paths: Paths) -> requests.Response:
    """Create a Zenodo record if it doesn't exist, or update one that does."""
    deposition_id = pystow.get_config(self.module, key)
    if deposition_id is not None:
        logger.info("Mapped local key %s to deposition %s", key, deposition_id)
        return update(self, deposition_id=deposition_id, data=data, paths=paths)

    res = create(self, data=data, paths=paths)
    # Write the ID to the key in the local configuration
    # so it doesn't need to be created from scratch next time
    pystow.write_config(self.module, key, str(res.json()["id"]))
    return res


def update(
    self: Zenodo, deposition_id: str, data: Data, paths: Paths
) -> requests.Response:
    """Create a new version of the given record with the given files."""

    current = requests.get(
        f"{self.depositions_base}/{deposition_id}",
        params={"access_token": self.access_token},
    )
    current.raise_for_status()
    current_data = current.json()
    current_version = current_data["metadata"]["version"]
    logger.info(
        f"Zenodo's version is {current_version}, local version is {data.version}"
    )
    if current_data["metadata"]["version"] == data.version:
        logger.info("No update necessary")
        return None

    # Prepare a new version based on the old version
    # see: https://developers.zenodo.org/#new-version)
    new_metadata = to_metadata_json(data)
    newversion_res = requests.post(
        f"{self.depositions_base}/{deposition_id}/actions/newversion",
        params={"access_token": self.access_token},
        json=new_metadata,
    )
    newversion_res.raise_for_status()
    new_deposition_data = newversion_res.json()
    logger.debug(f"newversion POST response: {pformat(new_deposition_data)}")

    new_deposition_url = new_deposition_data["links"]["latest_draft"]
    new_deposition_id = new_deposition_data["record_id"]
    new_metadata["metadata"]["publication_date"] = datetime.datetime.today().strftime(
        "%Y-%m-%d"
    )

    # Update the deposition for the new version
    # see: https://developers.zenodo.org/#update
    update_res = requests.put(
        new_deposition_url,
        json=new_metadata,
        params={"access_token": self.access_token},
    )
    update_res.raise_for_status()
    logger.debug(f"new_deposition_url PUT response: {pformat(update_res.json())}")

    # Upload new files. If no files have changed, there will be no update
    self._upload_files(bucket=newversion_res["links"]["bucket"], paths=paths)

    # Send the publish command
    return self.publish(new_deposition_id)


def to_metadata_json(data: Data) -> str:
    if isinstance(data, Metadata):
        return {
            "metadata": {
                key: value
                for key, value in data.model_dump(exclude_none=True).items()
                if value
            },
        }
    return data


def create(self: Zenodo, data: Data, paths: Paths) -> requests.Response:
    """Create a record.

    :param data: The JSON data to send to the new data
    :param paths: Paths to local files to upload
    :return: The response JSON from the Zenodo API
    :raises ValueError: if the response is missing a "bucket"
    """

    data = to_metadata_json(data)

    res_deposition = requests.post(
        self.depositions_base,
        json=data,
        params={"access_token": self.access_token},
    )
    res_deposition.raise_for_status()

    res_deposition_json = res_deposition.json()
    bucket = res_deposition_json.get("links", {}).get("bucket")
    if bucket is None:
        raise ValueError(f"No bucket in response. Got: {res_deposition_json}")

    logger.info("uploading files to bucket %s", bucket)
    self._upload_files(bucket=bucket, paths=paths)

    deposition_id = res_deposition_json["id"]
    logger.info("publishing files to deposition %s", deposition_id)

    res_publish = None
    sleep = 0
    retries = 0
    max_retries = 3
    while res_publish is None and retries < max_retries:
        if sleep > 0:
            time.sleep(sleep)
        try:
            res_publish = self.publish(deposition_id)
        except HTTPError as http_ex:
            code = http_ex.response.status_code
            if code == 504:
                logger.warning(f"Failed to publish due to 504")
            else:
                logger.fatal(f"Received HTTP {code}: {http_ex}")
            sleep = 5 if sleep == 0 else sleep * 2
            logger.warning(
                f"Retrying up to {max_retries-retries} more times, using {sleep}s back-off"
            )
            retries = retries + 1

    if res_publish:
        return res_publish
    else:
        return res_deposition


def upload(
    key: str, data: Metadata, paths: list[Union[str, Path]], sandbox=True
) -> requests.Response:
    """
    key     A unique key that you chose and that will be stored in
            ~/.config/zenodo.ini if your upload is successful
    """
    size = 0
    for p in paths:
        size += os.path.getsize(p)

    zen = Zenodo(access_token=ACCESS_TOKEN, sandbox=sandbox)
    logger.info(
        f"Trying to upload {sizeof_fmt(size)} for "
        f"'{key} ({data.title})' with version '{data.version}' "
        "to Zenodo..."
    )
    return ensure(
        zen,
        key=key,
        data=data,
        paths=paths,
    )


def get_available_licenses():
    import requests

    response = requests.get("https://zenodo.org/api/licenses/", params={"size": "200"})
    res_json = response.json()
    pprint(res_json)
    while "links" in res_json and "next" in res_json["links"]:
        response = requests.get(res_json["links"]["next"])
        res_json = response.json()
        pprint(res_json)


def create_metadata(toolname: str, version: str) -> Metadata:
    return Metadata(
        title=f"Ultimate {toolname} SV-COMP 2024",
        upload_type="software",
        description=f"""This is Ultimate {toolname}'s competition version for SV-COMP 2024. Visit <a href="https://github.com/ultimate-pa/ultimate">our Github repository</a> for the latest version or <a href="https://ultimate-pa.org">our website</a> to try it for yourself.""",
        creators=[
            creator(
                name="Dietsch, Daniel",
                orcid="0000-0002-8947-5373",
            ),
            creator(name="Bentele, Manuel", orcid="0009-0003-4794-958X"),
            creator(
                name="Heizmann, Matthias",
                orcid="0000-0003-4252-3558",
            ),
            creator(
                name="Klumpp, Dominik",
                orcid="0000-0003-4885-0728",
            ),
            creator(
                name="Podelski, Andreas",
                orcid="0000-0003-2540-9489",
            ),
            creator(
                name="Schüssele, Frank",
                orcid="0000-0002-5656-306X",
            ),
        ],
        version=version,
        license="lgpl-3.0-or-later",
    )


def upload_tools(args):
    tools = {
        "Automizer": "../UltimateAutomizer-linux.zip",
        "Kojak": "../UltimateKojak-linux.zip",
        # "Taipan": "../UltimateTaipan-linux.zip",
        # "GemCutter": "../UltimateGemCutter-linux.zip",
    }

    # it is enough to use Automizer's version
    output = subprocess.run(
        ["../UAutomizer-linux/Ultimate.py", "--ultversion"],
        check=True,
        capture_output=True,
        text=True,
    )
    m = re.search("This is Ultimate (\d+.\d+.\d+-\w+-\w+(-m)?)", output.stdout)
    if not m:
        logger.fatal(
            f"Could not determine version from Ultimate output: {output.stdout}"
        )
        sys.exit(1)
    version = m.groups(1)[0]
    logger.info(f"Found Ultimate version '{version}'")

    for tool, path in tools.items():
        if not os.path.exists(path):
            logger.warning(f"File {path} for {tool} does not exist, skipping")
            continue

        new_path = f"u{tool.lower()}.zip"
        os.rename(path, new_path)

        paths = [
            new_path,
        ]
        data = create_metadata(toolname=tool, version=version)
        try:
            result = upload(tool, data, paths, sandbox=args.sandbox)
            if result:
                logger.info(pformat(result.json()))
        except HTTPError as ex:
            logger.fatal(f"Upload failed with HTTP {ex.response.status_code}: {ex}")
            if ex.response.status_code >= 400:
                logger.fatal(pformat(ex.response.json()))
        os.rename(new_path, path)


# get_available_licenses()
args = parse_args()
upload_tools(args)
