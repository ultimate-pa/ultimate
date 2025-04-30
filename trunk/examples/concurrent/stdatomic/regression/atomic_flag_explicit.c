//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2025-04-30
 */

#include <stdatomic.h>

int main(void) {
  _Bool x = 0;
  _Bool y = atomic_test_and_set_explicit(&x, memory_order_seq_cst);
  //@ assert x == 1 && y == 0;
  atomic_clear_explicit(&x, memory_order_seq_cst);
  //@ assert x == 0;
}
