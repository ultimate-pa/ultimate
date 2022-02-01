//#Safe
/*
 * 
 */
#include<stdio.h>

struct stu {
  int a1[3][5];
} s1[4];


int main() {
  s1[0].a1[1][2] = 2;

  //printf("s1[0].a1[1]: %i\n", );

  if (s1[0].a1[0][0] != 0) {
    //@ assert \false;
  }
  if (s1[0].a1[1][0] != 0) {
    //@ assert \false;
  }

}
