////#Safe
/*
 * author: nutz
 */

#include<stddef.h>

int main() {
  int *p, i;
  p = malloc(4);
  i = (int) p;
  p = (int *) i;

  p = 0;
  i = (int) p;
  p = (int *) i;
 

  return 0;
}
