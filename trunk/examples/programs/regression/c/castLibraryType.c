//#Safe
/* 
 * Test where the parser misparses the cast to a function call (as the includes are ignored).
 * 
 * Author: schuessf@informatik.uni-freiburg.de
 * Date: 2025-12-15
 * 
 */

#include <stdint.h>

int main() {
  int x = __VERIFIER_nondet_int();
  long long y = (size_t)(x);
  if (y < 0) reach_error();
}
