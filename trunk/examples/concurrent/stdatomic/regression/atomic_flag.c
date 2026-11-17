//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2025-04-30
 */

#include <stdatomic.h>

int main(void) {
  _Bool x = 0;
  _Bool y = atomic_test_and_set(&x);
  //@ assert x == 1 && y == 0;
  atomic_clear(&x);
  //@ assert x == 0;
}
