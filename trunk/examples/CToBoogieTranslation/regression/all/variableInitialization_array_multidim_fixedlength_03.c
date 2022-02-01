//#Safe
#include<stdio.h>
int main() {
  int a[2][3] = { 1, 2, 3, 4 };

  printf("a[0][0]: %i\n", a[0][0]);
  printf("a[0][1]: %i\n", a[0][1]);
  printf("a[0][2]: %i\n", a[0][2]);
  printf("a[1][0]: %i\n", a[1][0]);
  printf("a[1][1]: %i\n", a[1][1]);
  printf("a[1][2]: %i\n", a[1][2]);

  int a00 = a[0][0];
  int a01 = a[0][1];
  int a02 = a[0][2];
  int a10 = a[1][0];
  int a11 = a[1][1];
  int a12 = a[1][2];

  if (a00 != 1) {
    //@assert \false;
  }
  if (a01 != 2) {
    //@assert \false;
  }
  if (a02 != 3) {
    //@assert \false;
  }
  if (a10 != 4) {
    //@assert \false;
  }
  if (a11 != 0) {
    //@assert \false;
  }
  if (a12 != 0) {
    //@assert \false;
  }


//  //@ assert a[0][0] == 1;
//  //@ assert a[0][1] == 2;
//  //@ assert a[0][2] == 3;
//  //@ assert a[1][0] == 4;
//  //@ assert a[1][1] == 0;
//  //@ assert a[1][2] == 0;
}
