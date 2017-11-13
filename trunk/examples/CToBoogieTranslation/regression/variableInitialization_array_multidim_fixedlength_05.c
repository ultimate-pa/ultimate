//#Safe
#include<stdio.h>
int main() {
  int a[2][3] = { 1, { 4, 5 }};

  printf("a[0][0]: %i\n", a[0][0]);
  printf("a[0][1]: %i\n", a[0][1]);
  printf("a[0][2]: %i\n", a[0][2]);
  printf("a[1][0]: %i\n", a[1][0]);
  printf("a[1][1]: %i\n", a[1][1]);
  printf("a[1][2]: %i\n", a[1][2]);

  //@ assert a[0][0] == 1;
  //@ assert a[0][1] == 4;
  //@ assert a[0][2] == 0;
  //@ assert a[1][0] == 0;
  //@ assert a[1][1] == 0;
  //@ assert a[1][2] == 0;
}
