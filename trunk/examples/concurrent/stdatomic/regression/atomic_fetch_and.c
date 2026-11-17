//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2025-04-30
 */

#include <stdatomic.h>

int main(void) {
  int x = 1;
  int y = atomic_fetch_and(&x, 0);
  //@ assert x == 0 && y == 1;
}
