//#Safe
/*
 * 
 */
#include<stdio.h>
int main() {
  struct stu {
    int i1;
    union { int i2; int *p1; };
  } s1 = { 0 };

  printf("s1.i1: %i\n", s1.i1);
  printf("s1.i2: %i", s1.i2);

  /*
   * C11 6.7.2.13:
   *  The members of an anonymous structure or union
   *  are considered to be members of the containing structure or union.
   */
  //@ assert s1.i1 == 0;
  //@ assert s1.i2 == 0;
}
