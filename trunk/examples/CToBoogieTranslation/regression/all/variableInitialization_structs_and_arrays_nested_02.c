//#Safe
/*
 * 
 */
#include<stdio.h>

struct stu {
  int a1[3][5];
} s1[4] = { 1 };


int main() {

  //printf("s1[0].a1[1]: %i\n", );

  if (s1[0].a1[0][0] != 1) {
    //@ assert \false;
  }
  if (s1[0].a1[1][0] != 0) {
    //@ assert \false;
  }

}
