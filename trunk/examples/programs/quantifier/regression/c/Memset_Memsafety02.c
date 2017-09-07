//#Unsafe
// regression test (5.01.2016)
// Author: nutz
//
#include <stdlib.h>

int nonmain() {
  int *jp = malloc(3 * sizeof(int) - 1);

  *jp = 4;

  jp++;

  memset(jp, 12345, 2 * sizeof(int));
}
