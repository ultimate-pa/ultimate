import re
import argparse
import os
from typing import List, Tuple
import xml.etree.ElementTree as ET

parser = argparse.ArgumentParser(
    description='filter results by cpu_time for all tools and generate merged sets for each architecture')
parser.add_argument('-i', '--input-dir', help='dir which contains xml files', required=True)
parser.add_argument('-t', '--max-time', help='cpu time filter, A single row will be excluded if the cpu time is >= for ALL captured cpu times', required=True)

"""
 <run files="[../../sv-benchmarks/c/array-examples/data_structures_set_multi_proc_ground-2.i]" name="../../sv-benchmarks/c/array-examples/data_structures_set_multi_proc_ground-2.yml" options="--traceabstraction.use.heuristic.emptiness.check true --traceabstraction.astar.heuristic.to.use.during.heuristic.emptiness.check ZERO --architecture 32bit" properties="unreach-call">
    <column title="cputime" value="300.975031405s"/>
    <column title="memory" value="978747392B"/>
    <column title="status" value="TIMEOUT"/>
    <column title="walltime" value="285.49068816937506s"/>
    <column hidden="true" title="category" value="error"/>
    <column hidden="true" title="cpuCores" value="4,20"/>
    <column hidden="true" title="cputime-cpu0" value="0.000205525s"/>
    <column hidden="true" title="cputime-cpu1" value="0.000338034s"/>
    <column hidden="true" title="cputime-cpu10" value="3.8712e-05s"/>
    <column hidden="true" title="cputime-cpu11" value="8.5672e-05s"/>
    <column hidden="true" title="cputime-cpu2" value="5.1226e-05s"/>
    <column hidden="true" title="cputime-cpu20" value="39.260144819s"/>
    <column hidden="true" title="cputime-cpu21" value="0.000197973s"/>
    <column hidden="true" title="cputime-cpu3" value="5.7289e-05s"/>
    <column hidden="true" title="cputime-cpu4" value="261.713629112s"/>
    <column hidden="true" title="cputime-cpu5" value="3.9344e-05s"/>
    <column hidden="true" title="cputime-cpu7" value="0.000121088s"/>
    <column hidden="true" title="cputime-cpu8" value="0.000122611s"/>
    <column hidden="true" title="exitsignal" value="9"/>
    <column hidden="true" title="memoryNodes" value="1"/>
    <column hidden="true" title="starttime" value="2020-04-20T19:32:02.671185+02:00"/>
    <column hidden="true" title="terminationreason" value="cputime"/>
  </run>
"""


class Run:
    def __init__(self, files, name, options, cputime, memory, status, walltime, category):
        self.files = files
        self.name = name
        self.options = options
        match = re.match(".*--architecture (32|64)bit.*", options)
        if match:
            arch = match.group(1)
            self.arch = arch
        else:
            self.arch = "32"
        self.cputime = cputime
        self.memory = memory
        self.status = status
        self.walltime = walltime
        self.category = category


def process_file(xml_file):
    print(f"processing {xml_file}")
    runs = []
    root = ET.parse(xml_file).getroot()
    for run in root.findall('run'):
        run_attribs = dict()
        for key, value in run.attrib.items():
            run_attribs[key] = value
        columns = list(run)
        for column in columns:
            run_attribs[column.attrib['title']] = column.attrib['value']
        runs.append(Run(files=run_attribs['files'].replace("[", "").replace("]", "").split(","),
                        name=run_attribs['name'],
                        options=run_attribs['options'],
                        cputime=float(run_attribs['cputime'].replace('s', '')),
                        memory=int(run_attribs['memory'].replace('B', '')),
                        status=run_attribs['status'],
                        walltime=float(run_attribs['walltime'].replace('s', '')),
                        category=run_attribs['category']))
    return runs


def process_dir(xml_file_dir):
    runs = []
    for file in os.listdir(xml_file_dir):
        if file.endswith(".xml"):
            full_path = xml_file_dir + "/" + file
            runs.extend(process_file(full_path))
    return runs


def filter_runs_by_cputime(runs: List[Run], cpu_time: float) -> Tuple[List[Run], List[Run]]:
    qualified = []
    unqualified = []
    for run in runs:
        if run.cputime < cpu_time:
            qualified.append(run)
        else:
            unqualified.append(run)
    return qualified, unqualified


if __name__ == "__main__":
    args = parser.parse_args()

    filter_time = int(args.max_time)
    input_dir = args.input_dir
    all_runs = process_dir(input_dir)
    file_to_runtimes = dict()
    for run in all_runs:
        file = run.files[0]
        yml = run.name
        arch = run.arch
        triple = (file,yml,arch)
        if triple not in file_to_runtimes:
            file_to_runtimes[triple] = []
        file_to_runtimes[triple].append(run.cputime)

    qualified = []
    unqualified = []
    for (file,yml,arch),cputimes in file_to_runtimes.items():
        if all([time >= filter_time for time in cputimes]):
            unqualified.append((file,yml,arch))
        else:
            qualified.append((file,yml,arch))

    #print(qualified)
    #print(unqualified)

    with open("64_set.set", "w+") as set64, open("32_set.set", "w+") as set32:
        for file,yml,arch in qualified:
            if arch == "64":
                set64.write(yml +"\n")
            else:
                set32.write(yml +"\n")









