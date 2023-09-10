//#Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-11-30
*/

int main() {
  int r, x, y;
  int* p;
  p = &x;
  if (y < 0) return;
  r = x & y;
  //@assert r >= 0;
}
