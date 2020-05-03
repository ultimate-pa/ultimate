import re
import csv
import argparse
import glob
import os
from pathlib import Path

parser = argparse.ArgumentParser(
    description='filter results by cpu_time for all tools and generate merged sets for each architecture')
parser.add_argument('-i', '--input', help='csv file which contains benchmark results', required=True)
parser.add_argument('-o', '--output-dir', help='output dir', required=True)
parser.add_argument('-t', '--time', help='cpu time filter, A single row will be excluded if the cpu time is >= for ALL tools in this row. ', required=True)
parser.add_argument('-sv', '--sv-benchmark-dir',
                    help='path to sv-bechmarks directory, which contains C programs', required=True)


class BenchmarkMaster:

    def __init__(self, sv_benchmark_dir):
        self.pattern_to_set = dict()
        self.set_to_arch = dict()
        self.generate_index(sv_benchmark_dir)

    def generate_index(self, sv_benchmark_dir):
        for file in os.listdir(sv_benchmark_dir):
            full_path = sv_benchmark_dir + "/" + file
            setname = os.path.basename(file).replace(".cfg", "").replace(".set", "")
            if not setname:
                print(f'skipping file {file}')
                continue
            if file.endswith(".cfg"):
                with open(full_path, "r") as cfg:
                    for row in cfg:
                        match = re.match(".*Architecture:.*(32|64).*", row)
                        if match:
                            arch = match.group(1)
                            self.set_to_arch[setname] = arch
            elif file.endswith(".set"):
                with open(full_path, "r") as setfile:
                    for line in setfile:
                        pattern = line.replace("\r\n", "").replace("\n", "").replace("\r", "").replace("*", ".*").strip()
                        if pattern:
                            print(pattern)
                            self.pattern_to_set[pattern] = setname

    def get_original_set(self, filename):
        for pattern, setname in self.pattern_to_set.items():
            if re.match(pattern, filename):
                print(f"{filename} matches {pattern} in set {setname}")
                return setname

    def get_original_arch(self, setname):
        print(f'set {setname}')
        return self.set_to_arch[setname]

    def generate_sets(self, output, output_dir, time):
        arch_to_files = dict()
        for outfile in output:
            original_set = self.get_original_set(outfile)
            if original_set:
                original_arch = self.get_original_arch(original_set)
                if original_arch not in arch_to_files:
                    arch_to_files[original_arch] = []
                arch_to_files[original_arch].append(outfile)
            else:
                print(f'{outfile} has no matching set')

        Path(output_dir).mkdir(parents=True, exist_ok=True)

        for arch, files in arch_to_files.items():
            prefix = f'{output_dir}/merged_{arch}_set'
            with open(f'{prefix}.set', "w+") as out_set, open(f'{prefix}.cfg', "w+") as out_cfg:
                for filename in files:
                    out_set.write(f'{filename}\n')
                description = f"Description: Contains tasks which have cpu time < {time} s"
                architecture = f"Architecture: {arch} bit"
                out_cfg.write(f"{description}\n{architecture}")

    def filter_by_time(self, input_file, time):
        output = []
        total_rows = 0
        with open(input_file, "r") as csv_file:
            reader = csv.reader(csv_file, delimiter="\t")
            next(reader)  # skip tools
            next(reader)  # skip sets
            header = next(reader)
            cpu_time_indices = [i for (i, r) in enumerate(
                header) if r.strip() == "cputime (s)"]
            for row in reader:
                total_rows += 1
                if not all([float(row[i]) >= float(time) for i in cpu_time_indices]):
                    output.append(row[0])
        print("\n".join(output))
        print(f"iterated over {total_rows} lines")
        print(f"output contains {len(output)} files")
        return output


if __name__ == "__main__":
    args = parser.parse_args()
    bm = BenchmarkMaster(args.sv_benchmark_dir)
    filtered = bm.filter_by_time(input_file=args.input, time=args.time)
    bm.generate_sets(filtered, args.output_dir, args.time)
