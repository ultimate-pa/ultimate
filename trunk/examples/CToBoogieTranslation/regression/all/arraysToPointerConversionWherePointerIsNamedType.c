////#Safe
/*
 * 
 *
 * author: nutz
 * date: 2014-10-16
 */

#include<stddef.h>

typedef int *iptr;

int main() {
  int a[3] = { 1, 2, 3 };
  iptr p;

  p = a;
  
  int i = *p;
  //@assert i == 1;

  return 0;
}
