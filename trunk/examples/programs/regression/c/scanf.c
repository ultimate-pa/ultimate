//#Unsafe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2023-02-21
*/
#include <stdio.h>

int main() {
  int x;
  int r = scanf("%d", &x);
  //@ assert r == 1 || x == 0;
}
