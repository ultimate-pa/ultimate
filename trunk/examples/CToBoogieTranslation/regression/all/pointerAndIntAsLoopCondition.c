////#Safe
/*
 * test that uses pointers and ints as a condition of a loop
 * author: nutz
 */

#include<stddef.h>

int main() {

  int *p;

  while (p) {
    p++;
  }

  int i;

  while (i) {
    i++;
  }

  return 0;
}
