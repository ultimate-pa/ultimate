//#Safe
/*  
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2024-09-27
 */

#include <ctype.h>

int main() {
  int x = __VERIFIER_nondet_uchar();
  int y = toupper(x);
  if (x >= 'a' && x <= 'z') {
    //@ assert y + 32 == x;
  } else {
    //@ assert x == y;
  }
}
