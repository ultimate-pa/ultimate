import os, shutil

for a, b, c in os.walk('.'):
 for fn in c:
  bv = 'Bitvector'
  bvIndex = fn.find(bv)
  fnew = fn[:bvIndex] + 'Float' + fn[bvIndex + len(bv):]
  print(fnew)
  shutil.move(os.path.join(a,fn), os.path.join(a,fnew))
