//#Safe
/*
 * Test created to expose the problem that by default our abstract 
 * interpretation does (currently) not allow us to derive relations 
 * between local variables from different scopes.
 * Related to issue #211.
 * The heap separator is not able to separate the array between pointers 
 * m1 and m2.
 *
 * author: Alexander Nutz
 */
#include <stdlib.h>

int * foo() {
  int* m1 =  malloc(4);
  *m1 = 5;
  return m1;
}

int * bar() {
  int* m2 =  malloc(4);
  *m2 = 7;
  return m2;
}

int main() {

  int * i = foo();
  int * j = bar();

  int v = *i;
  //@ assert v == 5;
}


