#!/usr/bin/python3

import collections
import json
import os

import os.path as osp


"""
Refresh the index used by the frontend to list available code examples per worker.

Run this script once you altered the content of the examples.
"""


SCRIPT_DIR = osp.abspath(osp.dirname(__file__))
WEBINTERFACE_EXAMPLES_ROOT = osp.join(SCRIPT_DIR, '..', '..', 'webinterface', 'code_examples')
MAX_NAME_LENGTH = 30  # Trim name below this threshold.


def refresh_index():
    print('Refreshing webinterface example index..')
    code_examples = collections.defaultdict(list)
    for folder in os.walk(WEBINTERFACE_EXAMPLES_ROOT):
        folder_name = osp.basename(folder[0])
        if folder_name == 'code_examples':
            continue
        for example in folder[2]:
            code_examples[folder_name].append({
                'name': (example[:MAX_NAME_LENGTH] + '...') if len(example) > MAX_NAME_LENGTH else example,
                'source': example
            })

    with open(osp.join(WEBINTERFACE_EXAMPLES_ROOT, 'code_examples.json'), mode='w') as out_file:
        json.dump(code_examples, out_file, indent=2)
    print('Done.')


if __name__ == "__main__":
    refresh_index()

