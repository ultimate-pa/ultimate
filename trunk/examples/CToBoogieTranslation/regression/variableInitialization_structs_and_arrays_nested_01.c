//#Safe
/*
 * 
 */
#include<stdio.h>
int main() {
  struct stu {
    int a1[3][5];
  } s1[4];

  s1[0].a1[1][2] = 2;

  //printf("s1[0].a1[1]: %i\n", );

  // assert s1.i1 == 0;
  // assert s1.i2 == 0;
}
