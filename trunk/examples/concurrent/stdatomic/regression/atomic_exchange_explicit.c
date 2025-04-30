//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2025-04-30
 */
 
#include <stdatomic.h>

int main(void) {
  int x = 0;
  int y = 1;
  int z = atomic_exchange_explicit(&x, y, memory_order_seq_cst);
  //@ assert x == 1 && y == 1 && z == 0;
}
