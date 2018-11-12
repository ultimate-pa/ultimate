////#Safe
/*
 * Test concerning treatment of unsigned ints. Both, in the normal case and when they are
 * used to store a pointer.
 * author: nutz
 * date: 2014-10-16
 */

#include<stddef.h>

int main() {

  unsigned int i, j;

  j = 0;
  i = j;
  j--;
  if (j <= i) {
    //@ assert \false;
  }

  int *p = malloc(sizeof(int)), *q = malloc(sizeof(int));
  unsigned int x, y;

  x = p;
  y = q;
  
  if (x == y) {
    //@ assert \false;
  }

  return 0;
}
