//#Safe
/*
 * author: Alexander Nutz
 */
#include <stdlib.h>

int main() {

  int *p = malloc(4);
  int *q = malloc(4);

  *p = 6;
  *q = 5;

  // array equality domain should be able to prove this safe
  //@ assert p != q; 

  int v = *p;
  // array equality domain should be able to prove this safe
  //@ assert v == 6;
}
