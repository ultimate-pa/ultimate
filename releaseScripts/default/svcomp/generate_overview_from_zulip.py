#!/usr/bin/env python3
# SVCOMP overview generation script for Ultimate tools.
# * Check Zulip messages for new results for Ultimate tools.
#   If there are new results, download XMLs from
#   https://sv-comp.sosy-lab.org/{args.year}/results/results-verified/results-per-tool.php
# * Use ultimate/releaseScripts/benchmark-processing/get-benchexec-overview.py
#   to generate an overview file per tool from new results.
# *  Move the overview file into the appropriate SVCOMP directory.
# *  Generate a list of all unsound files per tool and merge that list with the
#    existing unsound files stored in the current SVCOMP overview directory.


import argparse
import asyncio
from dataclasses import dataclass, asdict
import logging
from pathlib import Path
import re
import shutil
import subprocess
import sys
import textwrap
import aiohttp
import requests
from tqdm import tqdm
import zulip
import json
from datetime import datetime
from typing import List, Dict, Optional
import os
import lxml.html


@dataclass
class ZulipState:
    topic: str
    last_message_id: int
    seen_message_timestamps: list[int]


class ZulipTopicMonitor:
    def __init__(self, args: argparse.Namespace):
        self.client = zulip.Client(
            email=args.user, api_key=args.token, site=args.zulip_server
        )
        self.persistent_state_file = args.state_file
        self.topic_to_state: dict[str, ZulipState] = {}
        self.load_state()

    def get_stream_id(self, stream_name: str) -> Optional[int]:
        result = self.client.get_stream_id(stream_name)
        if result["result"] == "success":
            return result["stream_id"]
        else:
            logging.error(f"Error getting stream ID: {result['msg']}")
            return None

    def get_topics_in_stream(self, stream_id: int) -> List[Dict]:
        result = self.client.get_stream_topics(stream_id)
        if result["result"] == "success":
            return result["topics"]
        else:
            logging.error(f"Error getting topics: {result['msg']}")
            return []

    def find_topics_by_title(
        self, channel_name: str, topic_titles: List[str]
    ) -> List[Dict]:
        stream_id = self.get_stream_id(channel_name)
        if not stream_id:
            return []

        all_topics = self.get_topics_in_stream(stream_id)
        matching_topics = []

        for topic in all_topics:
            if topic["name"] in topic_titles:
                matching_topics.append(
                    {
                        "stream_id": stream_id,
                        "stream_name": channel_name,
                        "topic_name": topic["name"],
                    }
                )

        return matching_topics

    def get_messages_from_topic(
        self,
        stream_name: str,
        topic_name: str,
        anchor: str = "newest",
        num_messages: int = 100,
    ) -> List[Dict]:
        request = {
            "anchor": anchor,
            "num_before": num_messages if anchor == "newest" else 0,
            "num_after": 0 if anchor == "newest" else num_messages,
            "narrow": [
                {"operator": "stream", "operand": stream_name},
                {"operator": "topic", "operand": topic_name},
            ],
        }

        result = self.client.get_messages(request)
        if result["result"] == "success":
            return result["messages"]
        else:
            logging.error(f"Error getting messages: {result['msg']}")
            return []

    def get_new_messages(
        self, stream_name: str, topic_name: str
    ) -> tuple[list[dict], int | None]:
        """
        Get only new messages from a topic (messages after the last seen message)
        + the timestamp of the last non-new message (or none if none).
        """
        topic_key = f"{stream_name}::{topic_name}"
        if topic_key not in self.topic_to_state:
            topic_state = ZulipState(
                topic=topic_name, last_message_id=0, seen_message_timestamps=[]
            )
            self.topic_to_state[topic_key] = topic_state
        else:
            topic_state = self.topic_to_state[topic_key]
        last_seen_message_ts = (
            topic_state.seen_message_timestamps[-1]
            if topic_state.seen_message_timestamps
            else None
        )
        last_id = topic_state.last_message_id
        request = {
            "anchor": last_id,
            "num_before": 0,
            "num_after": 100,
            "narrow": [
                {"operator": "stream", "operand": stream_name},
                {"operator": "topic", "operand": topic_name},
            ],
        }
        result = self.client.get_messages(request)
        if result["result"] == "success":
            messages = result["messages"]
            # Filter out the anchor message itself if it was already seen
            new_messages = [msg for msg in messages if msg["id"] > last_id]

            if new_messages:
                topic_state.last_message_id = max(msg["id"] for msg in new_messages)
                for msg in new_messages:
                    topic_state.seen_message_timestamps.append(msg["timestamp"])

            return new_messages, last_seen_message_ts
        else:
            logging.error(f"Error getting messages: {result['msg']}")
            return [], last_seen_message_ts

    def load_state(self):
        state_file = self.persistent_state_file
        if os.path.exists(state_file):
            with open(state_file, "r") as f:
                data = json.load(f)
                self.topic_to_state = {k: ZulipState(**v) for k, v in data.items()}
            logging.info(f"Loaded state from {state_file}")

    def save_state(self):
        state_file = self.persistent_state_file
        # remove duplicate timestamps
        for state in self.topic_to_state.values():
            state.seen_message_timestamps = list(
                dict.fromkeys(state.seen_message_timestamps)
            )
        with open(state_file, "w") as f:
            json.dump(
                {k: asdict(v) for k, v in self.topic_to_state.items()}, f, indent=2
            )
        logging.info(f"Saved state to {state_file}")


@dataclass(frozen=True)
class ToolRun:
    tool: str
    date: str
    run_definition: str
    task_set: str
    fixed: bool
    validator: bool


@dataclass(frozen=True)
class ValidatorRun:
    verifier: str
    kind: str
    version: str
    validator: str
    date: str


class SVCOMPResultDownloader:
    base_url = "https://sv-comp.sosy-lab.org"
    get_verifier_runs_re = re.compile(
        r"([\w%-]+)\.(\d{4}-\d{2}-\d{2}_\d{2}-\d{2}-\d{2})\.results\.(SV-COMP\d{2}_[\w-]+).([\w.-]+?).xml.bz2(.fixed.xml.bz2)?.table.html"
    )
    get_validator_runs_loose_re = re.compile(
        r""""href": "..\/results-validated\/.*?.logfiles"""
    )
    get_validator_runs_re = re.compile(
        r""""href": "..\/results-validated\/([\w%.-]+)-validate-(violation|correctness)-witnesses-([12].0)-([\w%.-]+).(\d{4}-\d{2}-\d{2}_\d{2}-\d{2}-\d{2}).logfiles"""
    )

    def __init__(self, directory: Path, year: int):
        self.year = year
        self.base_url = f"{self.base_url}/{year}/results"
        self.download_directory = directory
        self._session = None
        self._verifier_runs_cache = None

    async def get_all_verifier_runs(self) -> List[ToolRun]:
        if self._verifier_runs_cache is not None:
            return self._verifier_runs_cache
        async with self._session.get(
            f"{self.base_url}/results-verified/results-per-tool.php"
        ) as response:
            response.raise_for_status()
            tree = lxml.html.fromstring(await response.text())
            ret = []
            for a_elem in tree.xpath("//a"):
                m = self.get_verifier_runs_re.fullmatch(a_elem.text)
                if m:
                    tool = m.group(1)
                    date = m.group(2)
                    run_definition = m.group(3)
                    task_set = m.group(4)
                    fixed = m.group(5) is not None
                    ret.append(
                        ToolRun(
                            tool=tool,
                            date=date,
                            run_definition=run_definition,
                            task_set=task_set,
                            fixed=fixed,
                            validator=False,
                        )
                    )
            self._verifier_runs_cache = ret
            return ret

    async def __aenter__(self):
        self._session = aiohttp.ClientSession()
        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        await self._session.close()

    async def _download(self, tool: str, filename: str, pbar):
        url = f"{self.base_url}/{filename}"
        async with self._session.get(url) as response:
            response.raise_for_status()
            filepath = self.download_directory / tool / filename
            filepath.parent.mkdir(parents=True, exist_ok=True)
            with open(filepath, "wb") as f:
                async for chunk in response.content.iter_chunked(8192):
                    f.write(chunk)
                    if pbar is not None:
                        pbar.update(len(chunk))

    async def _download_path(
        self, tool_name: str, is_validator: bool, filename: str, pbar
    ):
        filename = (
            f"results-validated/{filename}"
            if is_validator
            else f"results-verified/{filename}"
        )
        await self._download(tool_name, filename, pbar)

    async def download_tool_run_xml(self, tool_run: ToolRun, pbar=None):
        await self._download_path(
            tool_run.tool,
            tool_run.validator,
            f"{tool_run.tool}.{tool_run.date}.results.{tool_run.run_definition}.{tool_run.task_set}.xml.bz2{'.fixed.xml.bz2' if tool_run.fixed else ''}",
            pbar,
        )

    async def download_tool_run_logs(self, tool_name: str, date: str, pbar=None):
        await self._download_path(
            tool_name, False, f"{tool_name}.{date}.logfiles.zip", pbar
        )

    async def get_verifier_runs(self, verifier: str) -> List[ToolRun]:
        return [
            tool_run
            for tool_run in await self.get_all_verifier_runs()
            if tool_run.tool == verifier
        ]


async def download_new_results(
    downloader: SVCOMPResultDownloader,
    topic_name: str,
    message: dict,
    last_processed_ts: int | None,
):
    message_ts = int(message["timestamp"])

    def is_run_in_range(run: ValidatorRun) -> bool:
        run_ts = int(datetime.strptime(run.date, "%Y-%m-%d_%H-%M-%S").timestamp())
        if last_processed_ts is not None and run_ts <= last_processed_ts:
            logging.info(
                f"Skipping {run.tool} run from {run.date}: run older than last processed run ({datetime.fromtimestamp(last_processed_ts)})"
            )
            return False
        if message_ts < run_ts:
            logging.info(
                f"Skipping {run.tool} run from {run.date}: message older than run"
            )
            return False
        return True

    # download all XMLs and logfiles for this tool run
    runs = await downloader.get_verifier_runs(topic_name)
    download_tasks = []
    is_verifier = True
    with tqdm(
        unit="B",
        unit_scale=True,
        desc=f"Downloading result XMLs and logfiles for {topic_name}",
    ) as pbar:
        first_valid_run = None
        for run in runs:
            if not is_run_in_range(run):
                continue
            logging.debug(f"Downloading {run.tool} run from {run.date}")
            if not first_valid_run:
                first_valid_run = run
            download_tasks.append(downloader.download_tool_run_xml(run, pbar))
        if download_tasks:
            is_verifier = not first_valid_run.validator
            download_tasks.append(
                downloader.download_tool_run_logs(
                    first_valid_run.tool, first_valid_run.date, pbar
                )
            )
            await asyncio.gather(*download_tasks)
    return is_verifier, len(download_tasks) != 0


def process_new_results(
    tmp_dir: Path,
    topic_name: str,
    is_verifier: bool,
    other_scripts: Path,
    output_base_dir: Path,
    svcomp_year: int,
    message_ts: int,
) -> str:
    # tmp_dir/{tool_name}/results-verified contains the compressed XMLs and logfiles
    # getunsounds processes the decompressed XMLs, so we first decompress them
    tool_download_dir = (
        tmp_dir
        / topic_name
        / ("results-verified" if is_verifier else "results-validated")
    )

    logging.info("Extracting XML files")
    subprocess.run(
        f"bzip2 -d {tool_download_dir.as_posix()}/*.xml.bz2",
        shell=True,
        check=False,
    )

    logging.info("Computing unsound results")
    subprocess.run(
        f"{other_scripts.as_posix()}/getunsounds.py -d {tool_download_dir.as_posix()} | tee {tool_download_dir.as_posix()}/unsounds",
        shell=True,
        check=False,
    )
    # TODO: acumulate unsound files and merge with existing unsound files in SV-COMP overview directory
    # "${get_unsounds}" -f "${xmls}" -o "${unsounds}" -d . >> "${script_log}"

    logging.info("Extracting logfiles")
    subprocess.run(
        f"unzip -q {tool_download_dir.as_posix()}/*zip -d {tool_download_dir.as_posix()}",
        shell=True,
        check=False,
    )

    logging.info("Computing overview")
    subprocess.run(
        f"{other_scripts.as_posix()}/get-benchexec-overview.py -i {tool_download_dir.as_posix()} | tee {tool_download_dir.as_posix()}/overview",
        shell=True,
        check=False,
    )
    message_ts_str = datetime.fromtimestamp(message_ts).strftime("%Y%m%d-%H%M%S")
    output_dir = (
        output_base_dir
        / f"svcomp{svcomp_year}-{topic_name}"
        / f"{message_ts_str}-svcomp{svcomp_year}-{topic_name}-no-git"
    )
    logging.info(f"Moving results to {output_dir}")
    output_dir.parent.mkdir(parents=True, exist_ok=True)
    if output_dir.exists():
        shutil.rmtree(output_dir)
    shutil.copytree(tool_download_dir, output_dir, dirs_exist_ok=True)
    shutil.rmtree(tool_download_dir)

    return f"https://srv.dietsch.xyz/ultimate-logs/svcomp{svcomp_year}-{topic_name}/{message_ts_str}-svcomp{svcomp_year}-{topic_name}-no-git"


def get_mattermost_channel_id(server_url, token, team_name, channel_name):
    """Get channel ID from team name and channel name."""
    url = f"{server_url}/api/v4/teams/name/{team_name}/channels/name/{channel_name}"
    headers = {"Authorization": f"Bearer {token}", "Content-Type": "application/json"}
    response = requests.get(url, headers=headers)
    if response.status_code == 200:
        channel_data = response.json()
        return channel_data["id"]
    else:
        logging.error(f"Failed to get Mattermost channel ID: {response.status_code}")
        logging.error(response.text)
        return None


def send_mattermost_message(server_url, token, channel_id, message):
    """Send a message to a Mattermost channel."""
    url = f"{server_url}/api/v4/posts"
    headers = {"Authorization": f"Bearer {token}", "Content-Type": "application/json"}
    payload = {"channel_id": channel_id, "message": message}
    response = requests.post(url, json=payload, headers=headers)

    if response.status_code == 201:
        return True
    else:
        logging.error(f"Failed to send Mattermost message: {response.status_code}")
        logging.error(response.text)
        return False


def send_single_mattermost_message(args: argparse.Namespace, message):
    """Send a single message to the specified Mattermost channel.
    More expensive, because each call gets the channel ID first."""
    channel_id = get_mattermost_channel_id(
        args.mm_server, args.mm_token, *(args.mm_channel.split("/", 1))
    )
    send_mattermost_message(
        args.mm_server,
        args.mm_token,
        channel_id,
        message,
    )


async def main(args: argparse.Namespace):
    monitor = ZulipTopicMonitor(args)
    matching_topics = monitor.find_topics_by_title(args.channel_name, args.tools)
    if not matching_topics:
        logging.warning(f"No topics for any of {args.tools} found")
        return

    all_new_messages = []
    new_links = []
    async with SVCOMPResultDownloader(
        args.tmp_dir, 2000 + args.svcomp_year
    ) as downloader:
        for topic in matching_topics:
            topic_name = topic["topic_name"]
            new_messages, last_processed_ts = monitor.get_new_messages(
                topic["stream_name"], topic_name
            )
            if new_messages:
                logging.info(
                    f"{topic_name}: Found {len(new_messages)} new message(s), messages were last processed: {datetime.fromtimestamp(last_processed_ts) if last_processed_ts else 'never'}"
                )
                all_new_messages.extend(new_messages)
            else:
                logging.info(f"{topic_name}: No new messages")
                continue

            # determine date and download accordingly
            new_messages.sort(key=lambda msg: msg["timestamp"])
            for message in new_messages:
                message_ts = int(message["timestamp"])
                logging.info(
                    f"Processing message {message['id']} from topic {topic_name} ({datetime.fromtimestamp(message_ts)})"
                )
                is_verifier, has_new_results = await download_new_results(
                    downloader, topic_name, message, last_processed_ts
                )
                if has_new_results:
                    new_link = process_new_results(
                        args.tmp_dir,
                        topic_name,
                        is_verifier,
                        args.other_scripts,
                        args.output_base_dir,
                        args.svcomp_year,
                        message_ts,
                    )
                    new_links.append(new_link)

    monitor.save_state()
    if args.tmp_dir.exists():
        shutil.rmtree(args.tmp_dir)
    if new_links:
        msg = "**New SV-COMP results found!**\n"
        logging.info("New results available")
        for new_link in new_links:
            msg += f"- {new_link}\n"
            logging.info(new_link)
        if args.mm_token:
            send_single_mattermost_message(args, msg)


def token_string_or_file(arg):
    if not os.path.exists(arg):
        return arg
    else:
        return open(arg, "r").read().strip()


def parse_args():
    parser = argparse.ArgumentParser(
        description=textwrap.dedent("""
            SVCOMP overview generation script for Ultimate tools.
            * Checks Zulip messages for new results for Ultimate tools.
              If there are new results, downloads XMLs from
              https://sv-comp.sosy-lab.org/{args.year}/results/results-verified/results-per-tool.php
              Preserves the current state in a local file to avoid re-processing messages.
            * Uses ultimate/releaseScripts/benchmark-processing/get-benchexec-overview.py
              to generate an overview file per tool from new results.
            * Generates a list of all unsound files per tool and merge that list with the
              existing unsound files stored in the current SVCOMP overview directory.
            * Moves the overview and unsound files, the logfiles, and the XML files into an
              output directory.
"""),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--user",
        metavar="<file> or <user>",
        default=None,
        type=token_string_or_file,
        required=True,
        help="The login name for Zulip or a file containing it, e.g., your email "
        "address. Default: None",
    )
    parser.add_argument(
        "--token",
        metavar="<file> or <token>",
        default=None,
        type=token_string_or_file,
        required=True,
        help="The personal auth token for Zulip or a file containing it. Default: None",
    )
    parser.add_argument(
        "--zulip-server",
        metavar="<url>",
        default="https://competition.zulipchat.com",
        type=str,
        help="The Zulip URL. Default: https://competition.zulipchat.com",
    )
    parser.add_argument(
        "--state-file",
        metavar="<file>",
        default="zulip_state.json",
        type=Path,
        help="Path to a .json file where the script will store which messages "
        "are already processed. Default: ./zulip_state.json",
    )
    parser.add_argument(
        "--log-level",
        type=str.upper,
        choices=["DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL"],
        default="INFO",
        help="Set the logging level. Default: INFO",
    )
    channel_name_default = "SV-COMP Result Notifications"
    parser.add_argument(
        "--channel-name",
        type=str,
        default=channel_name_default,
        help=f"Name of the Zulip channel where we look for result topics. Default: {channel_name_default}",
    )

    parser.add_argument(
        "--tools",
        nargs="+",
        default=["uautomizer", "ukojak", "utaipan", "ugemcutter"],
        help="List of tool names (space-separated). Default: uautomizer ukojak utaipan ugemcutter",
    )

    parser.add_argument(
        "--tmp-dir",
        type=Path,
        default=Path("data"),
        help="Temporary directory for downloaded logs and XML files. Default: ./data",
    )

    parser.add_argument(
        "--output-base-dir",
        required=True,
        type=Path,
        help="Base directory for output logs.",
    )

    parser.add_argument(
        "--svcomp-year",
        required=True,
        type=int,
        help="SV-COMP year (e.g., 26 for 2026)",
    )

    parser.add_argument(
        "--other-scripts",
        type=Path,
        default=Path(__file__).parent.parent.parent / "benchmark-processing",
        help=f"Path to benchmark-processing scripts. Default: {Path(__file__).parent.parent.parent / 'benchmark-processing'}",
    )
    parser.add_argument(
        "--mm-server",
        default="https://chat.sopranium.de",
        help="Mattermost server URL. Default: https://chat.sopranium.de",
    )
    parser.add_argument(
        "--mm-token",
        type=token_string_or_file,
        help="Mattermost personal access token or bot token or a file containing it. "
        "If you supply it, the script will notify the specified Mattermost channel "
        "when it found new results. Default: None",
    )
    parser.add_argument(
        "--mm-channel",
        default="swt/ultimate",
        help="Channel name or team/channel format. Default: swt/ultimate",
    )

    args = parser.parse_args()
    logging.basicConfig(level=args.log_level, format="%(message)s", stream=sys.stdout)
    return args


if __name__ == "__main__":
    asyncio.run(main(parse_args()))
