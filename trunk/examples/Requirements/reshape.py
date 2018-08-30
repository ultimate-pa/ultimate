import os
import re
import shutil

path = os.getcwd()
print('Processing ' + path)

for (dirpath, dirnames, filenames) in os.walk(path):
    for file in filenames:
        if not file.endswith('.req'):
            continue
        with open(file) as f:

            lines = [line.rstrip('\n').strip() for line in f]

            idx = 0
            outlines = ''
            vars = set()
            for line in lines:
                outlines += 'ID{:03}: {}\n'.format(idx, line)
                vars.update(set(re.findall('x\d+', line)))
                idx = idx + 1

            outfile = open(file + '-tmp', 'w')
            for var in vars:
                outfile.write('Input {} is bool\n'.format(var))

            outfile.write('\n')
            outfile.writelines(outlines)
            outfile.close()

        shutil.move(file + '-tmp', file)
    break
