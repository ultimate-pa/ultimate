////#Safe
/*
 * this is a minimization of ldv-regression/test18... with respect
 * to the problem we seem to have with it right now..
 * the bug occurs when a function parameter that is a pointer is addressoffed.
 * in this case: we say (now, 2014-10-6: said) safe (which is correct) when the line &ip is commented out,
 * unsafe otherwise
 * author: nutz
 * date: 2014-10-03
 */

#include<stddef.h>

void f(int *ip) {
  *ip = 4;
  &ip;
}

int main() {

  int *p = malloc(sizeof(int));

  f(p);
  
  int i = *p;
  //@ assert i == 4;

  return 0;
}
