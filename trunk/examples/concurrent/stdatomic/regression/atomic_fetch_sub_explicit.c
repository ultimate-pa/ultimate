//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2025-04-30
 */

#include <stdatomic.h>

int main(void) {
  int x = 1;
  int y = atomic_fetch_sub_explicit(&x, 1, memory_order_seq_cst);
  //@ assert x == 0 && y == 1;
}
