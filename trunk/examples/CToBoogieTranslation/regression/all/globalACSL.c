////#Safe
/*
 * 
 *
 * author: nutz
 * date: 2014-11-17
 */


//@ ltl invariant positive: <>[] ! AP(x >= 0) <==> AP(x>=0) U AP(x<1) ==> ! X AP(x<1);
int x;

#include<stddef.h>


//@ requires 1 == 1;
int main() {

  x = 0;
  x = -1;
  x = 5;

  //@ assert x == 0;

  return 0;
}


//@ global invariant bla: x == 1;
