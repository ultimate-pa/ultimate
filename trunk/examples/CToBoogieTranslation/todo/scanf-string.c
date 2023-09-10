//#Unsafe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2023-02-21

  scanf is translated to exactly one write per argument. For strings however (using %s or %2c, %3c, ...)
  it is possible to write multiple bytes. Therefore the current translation is unsound in that case.
*/
#include <stdio.h>

int main() {
  char x[2];
  x[1] = 42;
  scanf("%2c", x);
  if (x[1] != 42) {
    //@ assert 0;
  }
}
