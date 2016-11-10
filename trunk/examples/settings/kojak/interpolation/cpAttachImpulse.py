import os, shutil

for a, b, c in os.walk('.'):
 for fn in c:
  fnew = fn[:-4] + '-Impulse.epf'
  shutil.copy(os.path.join(a,fn), os.path.join(a,fnew))
