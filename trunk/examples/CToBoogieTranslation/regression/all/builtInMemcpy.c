////#Safe
/*
 * 
 *
 * author: nutz
 * date: 2014-10-16
 */

#include<stddef.h>

int main() {

  struct s {
     int i;
     char c;
     int *p;
  } s1 = { 1, 'a', NULL}, s2;

  __builtin_memcpy(&s2, &s1, sizeof(struct s));
  
  int x = s1.i,y = s2.i;
  //@assert x == y;

  return 0;
}
