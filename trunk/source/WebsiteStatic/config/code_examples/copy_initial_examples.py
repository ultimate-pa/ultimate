import glob
import os
import shutil

import os.path as osp

""" This script
! Note: This script works only if run inside the ultimate repository.
Otherwise, the relative paths will fail.
 
* copies all code examples from a map (tool_examples_map) tool -> example_sources to the tool/example subfolder.

Add new examples for a worker.id in the `tool_examples_map`
Follow the rules already available.
"""

HERE = osp.abspath(osp.dirname(__file__))
PROJECT_ROOT = osp.join(HERE, '..', '..', '..', '..')
EXAMPLES_DIR = osp.join(PROJECT_ROOT, 'examples')


tool_examples_map = {
  'boogieAutomizer': [  # The worker.id as defined in config.js
    {
      'path': osp.join(EXAMPLES_DIR, 'programs', 'toy', 'showcase'),  # path to a folder containing examples.
      'pattern': '*.bpl'  # File name pattern (regex). Matches will be included.
    },
    {
      'path': osp.join(EXAMPLES_DIR, 'concurrent', 'bpl', 'regression', 'showcase'),
      'pattern': '*.bpl'
    }
  ],
  'boogieGemCutter': [
    {
      'path': osp.join(EXAMPLES_DIR, 'concurrent', 'bpl', 'regression', 'showcase'),
      'pattern': '*.bpl'
    }
  ],
  'cAutomizer': [
    {
      'path': osp.join(EXAMPLES_DIR, 'programs', 'toy', 'showcase'),
      'pattern': '*.c'
    },
    {
      'path': osp.join(EXAMPLES_DIR, 'programs', 'quantifier', 'regression', 'c'),
      'pattern': 'FunctionPointers01.c'
    }
  ],
  'cBuchiAutomizer': [
    {
      'path': osp.join(EXAMPLES_DIR, 'programs', 'termination', 'showcase'),
      'pattern': '*.c'
    }
  ],
  'boogieBuchiAutomizer': [
    {
      'path': osp.join(EXAMPLES_DIR, 'programs', 'termination', 'showcase'),
      'pattern': '*.bpl'
    }
  ],
  'cKojak': [
    {
      'path': osp.join(EXAMPLES_DIR, 'programs', 'toy', 'showcase'),
      'pattern': '*.c'
    },
    {
      'path': osp.join(EXAMPLES_DIR, 'programs', 'quantifier', 'regression', 'c'),
      'pattern': 'FunctionPointers01.c'
    }
  ],
  'boogieKojak': [
    {
      'path': osp.join(EXAMPLES_DIR, 'programs', 'toy', 'showcase'),
      'pattern': '*.bpl'
    }
  ],
  'cTaipan': [
    {
      'path': osp.join(EXAMPLES_DIR, 'programs', 'toy', 'showcase'),
      'pattern': '*.c'
    },
    {
      'path': osp.join(EXAMPLES_DIR, 'programs', 'quantifier', 'regression', 'c'),
      'pattern': 'FunctionPointers01.c'
    }
  ],
  'boogieTaipan': [
    {
      'path': osp.join(EXAMPLES_DIR, 'programs', 'toy', 'showcase'),
      'pattern': '*.bpl'
    }
  ],
  'cLTLAutomizer': [
    {
      'path': osp.join(EXAMPLES_DIR, 'LTL', 'coolant'),
      'pattern': '*'
    },
  ],
  'cLassoRanker': [
    {
      'path': osp.join(EXAMPLES_DIR, 'lassos'),
      'pattern': '*.c'
    },
  ],
  'boogieLassoRanker': [
    {
      'path': osp.join(EXAMPLES_DIR, 'lassos'),
      'pattern': '*.bpl'
    },
    {
      'path': osp.join(EXAMPLES_DIR, 'lassos', 'website'),
      'pattern': '*.bpl'
    },
  ],
  'automataScript': [
    {
      'path': osp.join(EXAMPLES_DIR, 'Automata', 'website'),
      'pattern': '*.ats'
    },
  ],
  'cReferee': [
    {
      'path': osp.join(EXAMPLES_DIR, 'programs', 'toy', 'InvariantChecking', 'showcase'),
      'pattern': '*.c'
    },
  ],
  'boogieReferee': [
    {
      'path': osp.join(EXAMPLES_DIR, 'programs', 'toy', 'InvariantChecking', 'showcase'),
      'pattern': '*.bpl'
    },
  ],
  'smtEliminator': [
    {
      'path': osp.join(EXAMPLES_DIR, 'smtlib', 'QuantifierElimination'),
      'pattern': '*.smt2'
    },
  ],
}


if __name__ == '__main__':
    for tool in tool_examples_map.keys():
        dest = osp.join(HERE, tool)
        if not osp.exists(dest):
            os.makedirs(dest)

    print('Start copying examples.')
    for tool, examples in tool_examples_map.items():
        for example in examples:
            path = example['path']
            pattern = example['pattern']
            dest = osp.join(HERE, tool)
            for file in glob.glob(rf'{path}/{pattern}'):
                shutil.copy(file, dest)
    print('Done.')
