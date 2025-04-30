//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2025-04-30
 */

#include <stdatomic.h>

int main(void) {
  int x = 1;
  int y = atomic_load_explicit(&x, memory_order_seq_cst);
  //@ assert x == 1 && y == 1;
}
