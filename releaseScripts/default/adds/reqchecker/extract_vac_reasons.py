import argparse
import os
import re

def parseArguments():
  parser = argparse.ArgumentParser()
  parser.add_argument('orig_req_file', metavar='orig-req-file', type=str,
    help='Original requirement file. (*.req)')
  parser.add_argument('ultimate_log', metavar='ultimate-log', type=str,
    help='The log Ultimate produced when analyzing the requirements file.')
  parser.add_argument('requirement_repo', metavar='requirement-repo', type=str,
    help='The path to the repository which contains the requirements folder.')

  args = parser.parse_args()

  # Do not change, except you know what you are doing.
  args.explode = 'explode_script.py'
  args.tmp_dump_dir = 'dump-ss'
  args.dump_dir = 'dump'

  print('PARAMETERS:')
  print('- orig-req-file:', args.orig_req_file)
  print('- ultimate-log:', args.ultimate_log)
  print('- requirement-repo:', args.requirement_repo)
  print('- explode:', args.explode)
  print('- tmp-dump-dir:', args.tmp_dump_dir)
  print('- dump-dir:', args.dump_dir)
  print()

  # Check arguments.
  for directory in [args.requirement_repo]:
    if not os.path.isdir(directory):
      raise ValueError('Could not find directory: %s' % directory)

  for file in [args.orig_req_file, args.ultimate_log, args.explode]:
    if not os.path.isfile(file):
      raise ValueError('Could not find file: %s' % file)

  return args


def parseResults(args):
  results = []
  with open(args.ultimate_log, 'r') as logfile:
    results = [i.split(' ')[1] for i in re.findall('Requirement .* is vacuous', logfile.read())]

  return results


def main():
  args = parseArguments()
  results = parseResults(args)

  print('Number of vacuous results:', len(results))

  for result in results:
    reduced_req_file = result + '.vac.req'

    print()
    print('Processing:', result)


if __name__ == "__main__":
  main()