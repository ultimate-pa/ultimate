import argparse
import os
import shutil
import subprocess
import re

def parseArguments():
  parser = argparse.ArgumentParser()

  parser.add_argument('req_file', metavar='req-file', type=str, help='Reqirement file. (*.req)')
  parser.add_argument('req_repo_folder', metavar='req-repo-folder', type=str,
    help='The path to the repository which contains the requirements folder.')
  parser.add_argument('req_folder', type=str, metavar='req-folder',
    help='The path to the requirements folder.')
  parser.add_argument('--rt-inconsistency-range', type=int, default=2,
    help='The amount of requirements which are checked together for RT-inconsistency. (default: 2)')
  parser.add_argument('--timeout-per-assertion', type=int, default=900,
    help='Amount of seconds until analysis of an assertion is timed out. (default: 900)')

  args = parser.parse_args()

  # Don't touch this, unless you know what you are doing.
  args.automizer_folder = '.'
  args.ultimate_binary = args.automizer_folder + '/plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar'
  # Path to the vacuity extractor script.
  args.vac_extractor = './extract_vac_reasons.sh'
  # Path to Ultimate Automizer (remember those binaries we created earlier? that's what you want!).
  args.reqcheck_toolchain = './config/ReqCheck.xml'
  args.reqcheck_settings = './config/ReqCheck-nonlin.epf'
  args.testgen_toolchain = './config/ReqToTest.xml'
  args.testgen_settings = './config/ReqCheck-ReqToTest.epf'

  print('PARAMETERS:')
  print('- req-file:', args.req_file)
  print('- req-repo-folder:', args.req_repo_folder)
  print('- req-folder:', args.req_folder)
  print('- rt-inconsistency-range:', args.rt_inconsistency_range)
  print('- timeout-per-assertion:', args.timeout_per_assertion)

  print('- automizer-folder:', args.automizer_folder)
  print('- ultimate-binary:', args.ultimate_binary)
  print('- vac-extractor:', args.vac_extractor)
  print('- reqcheck-toolchain:', args.reqcheck_toolchain)
  print('- reqcheck-settings:', args.reqcheck_settings)
  print('- testgen-toolchain:', args.testgen_toolchain)
  print('- testgen-settings:', args.testgen_settings)

  # Check arguments.
  for directory in [args.req_repo_folder, args.req_folder, args.automizer_folder]:
    if not os.path.isdir(directory):
      raise ValueError('Could not find directory: %s' % directory)

  for file in [args.req_file, args.ultimate_binary, args.vac_extractor, args.reqcheck_toolchain, args.reqcheck_settings,
      args.testgen_toolchain, args.testgen_settings]:
    if not os.path.isfile(file):
      raise ValueError('Could not find file: %s' % file)

  return args


def prepare_dirs(dirs):
  for d in dirs:
    if os.path.isdir(d):
      continue

    if 'y' != input('%s does not exist, should I create it? (y / n): ' % d):
      print('Exiting now.')
      exit(2)

    os.makedirs(d)
    print('Succesfully created: %s' % d)


def run_reqcheck(args):
  #os.chdir(args.automizer_folder)
  #cwd = os.getcwd()

  dump_folder = args.automizer_folder + '/dump-' + args.req_filename + args.req_extension
  if os.path.isdir(dump_folder):
    if 'y' != input('Found existing dump folder: %s. Should I delete it? (y / n): ' % dump_folder):
      print('Exiting now.')
      exit(1)

    shutil.rmtree(dump_folder)

  if os.path.isfile(args.reqcheck_log):
    if 'y' != input('Found existing logfile: %s. Should I delete it? (y / n): ' % args.reqcheck_log):
      print('Exiting now.')
      exit(1)

    os.remove(args.reqcheck_log)

  print()
  print('Analyzing:', args.req_file)
  print('Using logfile:', args.reqcheck_log)
  print()
  os.mkdir(dump_folder)

  log = subprocess.check_output(
    'java ' \
    '-Dosgi.configuration.area=config/ ' \
    '-Xmx100G ' \
    '-Xss4m ' \
    '-jar plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar ' \
    '-tc ' + args.reqcheck_toolchain + ' ' \
    '-s ' + args.reqcheck_settings + ' ' \
    '-i ' + args.req_file + ' ' \
    '--core.print.statistic.results false ' \
    '--traceabstraction.dump.smt.script.to.file true ' \
    '--traceabstraction.to.the.following.directory=' + dump_folder + ' ' \
    '--traceabstraction.limit.analysis.time ' + str(args.timeout_per_assertion) + ' ' \
    '--pea2boogie.always.use.all.invariants.during.rt-inconsistency.checks true ' \
    '--pea2boogie.check.vacuity true ' \
    '--pea2boogie.check.consistency true ' \
    '--pea2boogie.check.rt-inconsistency true ' \
    '--pea2boogie.report.trivial.rt-consistency false ' \
    '--pea2boogie.rt-inconsistency.range ' + str(args.rt_inconsistency_range),
    shell=True
  )

  with open(args.reqcheck_log, 'wb+') as logfile:
    logfile.write(log)

  # Postprocess results with vacuity extractor.
  if not os.path.isfile(args.reqcheck_log):
    print('Logfile was not created.')
    exit(1)

  print('Extracting results to:', args.reqcheck_relevant_log)

  is_vacuous = False
  with open(args.reqcheck_log, 'r') as logfile:
    excludes = 'StatisticsResult|ReqCheckSuccessResult'
    matches = [i for i in re.findall('  - .*', logfile.read()) if not re.search(excludes, i)]
    relevant_log = os.linesep.join(matches)
    is_vacuous = 'vacuous' in relevant_log

    with open(args.reqcheck_relevant_log, 'w+') as relevant_logfile:
      relevant_logfile.write(relevant_log)

  # TODO: Call vac_extractor python
  if is_vacuous:
    print('Analyzing reasons for vacuity.')
    subprocess.call(
      args.vac_extractor + ' ' + \
      args.req_file + ' ' + \
      args.reqcheck_log + ' ' + \
      args.req_repo_folder + ' ' \
      ' ' # TODO: remove that
    )
    shutil.move('*.vac.req', args.log_folder)
  
  if not is_vacuous:
    print('No vacuities found.')


def run_testgen(args):
  print('Using logfile:', args.testgen_log)

  log = subprocess.check_output(
    'java ' \
    '-Dosgi.configuration.area=config/ ' \
    '-Xmx100G ' \
    '-Xss4m ' \
    '-jar plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar ' \
    '-tc ' + args.testgen_toolchain + ' ' \
    '-s ' + args.testgen_settings + ' ' \
    '-i ' + args.req_file + ' ' \
    '--core.print.statistic.results false ' \
    '--rcfgbuilder.simplify.code.blocks false ' \
    '--rcfgbuilder.size.of.a.code.block LoopFreeBlock ' \
    '--traceabstraction.limit.analysis.time ' + str(args.timeout_per_assertion) + ' ' \
    '--rcfgbuilder.add.additional.assume.for.each.assert false',
    shell=True
  )

  relevant_log = re.sub('(.|\n|\r\n)*--- Results ---', '--- Results ---', log.decode('utf-8'))

  with open(args.testgen_log, 'wb+') as logfile:
    logfile.write(log)

  with open(args.testgen_relevant_log, 'w+') as relevant_logfile:
    relevant_logfile.write(relevant_log)


def main():
  args = parseArguments()

  args.req_filename, args.req_extension = os.path.splitext(os.path.basename(args.req_file))
  args.reqcheck_log = args.req_folder + '/' + args.req_filename + args.req_extension + '.log'
  args.testgen_log = args.req_folder + '/' + args.req_filename + args.req_extension + '.testgen.log'
  args.log_folder = args.req_folder + '/logs/' + args.req_filename
  args.reqcheck_relevant_log = args.log_folder + '/' + args.req_filename + args.req_extension + '.relevant.log'
  args.testgen_relevant_log = args.log_folder + '/' + args.req_filename + args.req_extension + '.testgen.log'

  print()
  print('- reqcheck_log:', args.reqcheck_log)
  print('- testgen_log:', args.testgen_log)
  print('- log_folder:', args.log_folder)
  print('- reqcheck_relevant_log:', args.reqcheck_relevant_log)
  print('- testgen_relevant_log:', args.testgen_relevant_log)
  print()

  prepare_dirs([args.log_folder])

  print('Running ReqChecker.')
  run_reqcheck(args)

  print('Running TestGen.')
  run_testgen(args)


if __name__ == "__main__":
  main()