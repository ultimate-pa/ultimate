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
from requests import JSONDecodeError
from zenodo_client import Creator, Metadata, Zenodo
from zenodo_client.api import Data, Paths
import pystow

from ruamel.yaml import YAML

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
        action=argparse.BooleanOptionalAction,
        default=True,
        type=bool,
        help="Should we use Zenodo's sandbox instead of the real Zenodo? Default: Yes",
    )
    parser.add_argument(
        "--fm-tools-repo",
        dest="fmtools_path",
        metavar="<dir>",
        help="Update YAML files with new Zenodo DOI. Default: None",
    )
    parser.add_argument(
        "--svcomp",
        dest="year",
        metavar="<year>",
        help=f"Which SVCOMP version should be updated in the YAML files. Default: {datetime.datetime.today().year+1}",
        default=str(datetime.datetime.today().year + 1),
    )

    args = parser.parse_args()

    global ACCESS_TOKEN
    ACCESS_TOKEN = os.environ.get(
        "ZENODO_PERSONAL_API_TOKEN", token_string_or_file(args.token)
    )
    os.environ["ZENODO_SANDBOX_API_TOKEN"] = ACCESS_TOKEN
    logger.setLevel(logging.INFO)
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
        res = update(self, deposition_id=deposition_id, data=data, paths=paths)
        if res:
            pystow.write_config(self.module, key, str(res.json()["id"]))
        return res

    res = create(self, data=data, paths=paths)
    # Write the ID to the key in the local configuration
    # so it doesn't need to be created from scratch next time
    pystow.write_config(self.module, key, str(res.json()["id"]))
    return res


def update(
    self: Zenodo, deposition_id: str, data: Data, paths: Paths
) -> requests.Response:
    """Create a new version of the given record with the given files."""

    def get_current(id):
        current = requests.get(
            f"{self.depositions_base}/{id}",
            params={"access_token": self.access_token},
        )
        current.raise_for_status()
        return current

    current = retry_request(lambda: get_current(deposition_id), "Get Current")
    if not current:
        logger.fatal(f"Could not get deposition {deposition_id}, giving up")
        return None

    current_data = current.json()
    logger.debug(f"get_current({deposition_id}) GET response: {pformat(current_data)}")

    if current_data["conceptrecid"] != deposition_id:
        logger.warning(
            f"The main deposition for this record is {current_data['conceptrecid']}"
        )
        # return update(self, current_data["conceptrecid"], data, paths)

    current_version = current_data["metadata"]["version"]
    logger.info(
        f"Zenodo's version for {deposition_id} is {current_version}, local version is {data.version}. Zenodo's 'latest' is at {current_data['links']['latest_html']}"
    )
    if current_version == data.version:
        logger.info("No update necessary")
        return current

    new_metadata = to_metadata_json(data)

    def create_new_version():
        # Prepare a new version based on the old version
        # see: https://developers.zenodo.org/#new-version)
        newversion_res = requests.post(
            f"{self.depositions_base}/{deposition_id}/actions/newversion",
            params={"access_token": self.access_token},
            json=new_metadata,
        )
        newversion_res.raise_for_status()
        return newversion_res

    newversion_res = retry_request(create_new_version, "Create new version")
    if not newversion_res:
        logger.fatal(
            f"Failed to create new version for deposition {deposition_id}, giving up"
        )
        return None

    newversion_data = newversion_res.json()
    logger.debug(f"create_new_version() POST response: {pformat(newversion_data)}")
    new_deposition_url = newversion_data["links"]["latest_draft"]
    new_deposition_id = newversion_data["record_id"]
    new_metadata["metadata"]["publication_date"] = datetime.datetime.today().strftime(
        "%Y-%m-%d"
    )

    def populate_new_version():
        # Update the deposition for the new version
        # see: https://developers.zenodo.org/#update
        update_res = requests.put(
            new_deposition_url,
            json=new_metadata,
            params={"access_token": self.access_token},
        )
        update_res.raise_for_status()
        return update_res

    update_res = retry_request(populate_new_version, "Populate new version")
    logger.debug(f"populate_new_version PUT response: {pformat(update_res.json())}")

    # Upload new files. If no files have changed, there will be no update
    self._upload_files(bucket=newversion_data["links"]["bucket"], paths=paths)

    # Send the publish command
    return retry_request(lambda: self.publish(new_deposition_id), "Publishing")


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


def log_request_error(fun, desc: str):
    try:
        return fun()
    except HTTPError as http_ex:
        code = http_ex.response.status_code
        if code == 504:
            logger.warning(f"{desc}: Failed with 504")
        else:
            logger.fatal(f"{desc}: Failed with HTTP {code}: {http_ex}")
            try:
                as_json = http_ex.response.json()
                logger.fatal(f"{desc}: {pformat(as_json)}")
            except JSONDecodeError:
                logger.fatal(
                    f"{desc}: No valid JSON in {code} response: {http_ex.response.text}"
                )
        return http_ex.response


def retry_request(fun, desc: str, max_retries=3, init_sleep=5):
    response = None
    sleep = 0
    retries = 0
    while response is None and retries < max_retries:
        if retries > 0:
            logger.warning(
                f"{desc}: Retrying up to {max_retries-retries} more times, using {sleep}s back-off"
            )
        if sleep > 0:
            time.sleep(sleep)
        response = log_request_error(fun, desc)
        if response.status_code >= 500:
            sleep = init_sleep if sleep == 0 else sleep * 2
            retries = retries + 1
            response = None
        elif response.ok:
            break

    if response and response.ok and retries > 0:
        logger.warning(
            f"{desc}: Successful after {retries} retries with {response.status_code}"
        )
    logger.debug(response.status_code)
    return response


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
    logger.info("Publishing files to deposition %s", deposition_id)

    res_publish = retry_request(lambda: self.publish(deposition_id), "Publishing")

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


def upload_tools(args, tools):
    # it is enough to use Automizer's version
    automizer_py = Path(tools["Automizer"]).parent / "UAutomizer-linux" / "Ultimate.py"
    if not automizer_py.exists():
        logger.fatal(
            "Did not find Automizer's directory relative to .zip file."
            f"This script assumes {automizer_py} exists."
        )
        sys.exit(1)
    output = subprocess.run(
        [automizer_py.absolute(), "--ultversion"],
        check=True,
        capture_output=True,
        text=True,
    )
    m = re.search(r"This is Ultimate (\d+.\d+.\d+-\w+-\w+(-m)?)", output.stdout)
    if not m:
        logger.fatal(
            f"Could not determine version from Ultimate output: {output.stdout}"
        )
        sys.exit(1)
    version = m.groups(1)[0]
    logger.info(f"Found Ultimate version '{version}'")
    logger.info("--")
    tool_to_doi = {}
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
        result = log_request_error(
            lambda: upload(tool, data, paths, sandbox=args.sandbox), "Upload"
        )
        if result and result.ok:
            data = result.json()
            if "doi" in data:
                doi = data["doi"]
                url = data["links"]["html"]
                logger.info(
                    f"Success: DOI for {tool} with version {version} is {doi} at {url}"
                )
                tool_to_doi[tool] = doi = data["doi"]
            logger.debug(pformat(data))
        os.rename(new_path, path)
        logger.info("--")
    return tool_to_doi


def create_metadata(toolname: str, version: str) -> Metadata:
    return Metadata(
        title=f"Ultimate {toolname} SV-COMP 2025",
        upload_type="software",
        description=f"""This is Ultimate {toolname}'s competition version for SV-COMP 2025. Visit <a href="https://github.com/ultimate-pa/ultimate">our Github repository</a> for the latest version or <a href="https://ultimate-pa.org">our website</a> to try it for yourself.""",
        creators=[
            creator(
                name="Dietsch, Daniel",
                orcid="0000-0002-8947-5373",
            ),
            creator(name="Bentele, Manuel", orcid="0009-0003-4794-958X"),
            creator(
                name="Ebbinghaus, Marcel",
            ),
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


def tool_zip(tool: str):
    """.zip of tool"""
    return f"/storage/repos/ultimate-2/releaseScripts/default/Ultimate{tool}-linux.zip"


def tool_yaml(tool: str):
    """YAML file relative to fm-tools repo"""
    return f"data/u{tool.lower()}.yml"


# get_available_licenses()
args = parse_args()

tool_names = ["Automizer", "Kojak", "Taipan", "GemCutter", "Referee"]
tools = {k: tool_zip(k) for k in tool_names}
yaml_files = {k: tool_yaml(k) for k in tool_names}

tool_to_doi = upload_tools(args, tools)
if args.fmtools_path:
    p = Path(args.fmtools_path)
    if p.is_dir() and p.exists():
        for tool, f in yaml_files.items():
            if tool not in tool_to_doi:
                logger.error(f"No DOI for {tool}, skipping")
                continue
            yaml_file = p / Path(f)
            if not yaml_file.is_file() or not yaml_file.exists():
                logger.error(f"{yaml_file} for {tool} does not exist, skipping")
                continue
            content = None
            with open(yaml_file, "r") as file:
                yaml = YAML()
                content = yaml.load(file)
            if content["name"][1:].lower() != tool.lower():
                logger.error(
                    f"{yaml_file} for {tool} is actually for {content['name']}, skipping"
                )
                continue
            if "versions" not in content:
                logger.error(f"{yaml_file} for {tool} does not have 'versions' section")
                continue

            dump_yaml = False

            def replace_if_matching(version):
                global dump_yaml
                target_ver = f"svcomp{args.year[2:]}"
                if target_ver in version["version"]:
                    new = version
                    new["doi"] = tool_to_doi[tool]
                    logger.info(f'Updated {tool} {version["version"]} to {new["doi"]}')
                    dump_yaml = True
                    return new
                return version

            content["versions"] = [replace_if_matching(c) for c in content["versions"]]

            if dump_yaml:
                with open(yaml_file, "w") as f:
                    yaml = YAML()
                    yaml.default_flow_style = False
                    yaml.dump(content, f)
                    logger.info(f"Updated {yaml_file} for {tool} with new DOI(s)")
