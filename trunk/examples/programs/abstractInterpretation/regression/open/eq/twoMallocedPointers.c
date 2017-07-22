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

  //@ assert p != q;

  int v = *p;
  //@ assert v == 6;
}
