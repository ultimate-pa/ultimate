////#Safe
/*
 * author: nutz
 * date: 2014-10-06
 */

#include<stddef.h>


int main() {
  union u {
   int i;
   int j;
   char c;
  } u1;

  &u1;

  u1.i = 2;
  int x = u1.c;
  //@ assert x == 2;

  return 0;
}
