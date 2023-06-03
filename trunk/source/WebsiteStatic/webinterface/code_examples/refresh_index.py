import collections
import json
import os

import os.path as osp


""" Refresh the index used by the frontend to list available code examples per worker.

* Run this script once you altered the content of the examples.

"""


HERE = osp.abspath(osp.dirname(__file__))
MAX_NAME_LENGTH = 30  # Trim name below this threshold.

code_examples = collections.defaultdict(list)
for folder in os.walk(HERE):
    folder_name = osp.basename(folder[0])
    if folder_name == 'code_examples':
        continue
    for example in folder[2]:
        code_examples[folder_name].append({
            'name': (example[:MAX_NAME_LENGTH] + '...') if len(example) > MAX_NAME_LENGTH else example,
            'source': example
        })

with open(osp.join(HERE, 'code_examples.json'), mode='w') as out_file:
    json.dump(code_examples, out_file, indent=2)
