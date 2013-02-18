/*
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Implementation of McCarthy's 91 function. The program is correct with
 * respect to assertions.
 *
 * The example is taken from our POPL'10 paper "Nested Interpolants".
 */
#include <vcc.h>

int mcCarthy(int x)
{
  int res;
  if (x>100) {
    res = x-10;
  }
  else {
    res = mcCarthy(x + 11);
    res = mcCarthy(res);
  }
  assert(res == 91 || x > 101);
}

