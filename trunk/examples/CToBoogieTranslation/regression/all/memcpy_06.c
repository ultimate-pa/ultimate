//#Safe
/*
 * Test for memcpy, inspired by strcpy_01.c
 */
#include<string.h>
#include<stdio.h>
int main() {
  short a[6] = { 1, 2, 0, 0, 0, 0 };

  //memcpy(a + (3* sizeof(short)), a, 3 * sizeof(short));
  memcpy(a + 3, a, 2* sizeof(short));

//  printf("a[0]: %hi\n", a[0]);
//  printf("a[1]: %hi\n", a[1]);
//  printf("a[2]: %hi\n", a[2]);
//  printf("a[3]: %hi\n", a[3]);
//  printf("a[4]: %hi\n", a[4]);
//  printf("a[5]: %hi\n", a[5]);

  if (a[0] != 1) {
    //@ assert \false;
  }
  if (a[1] != 2) {
    //@ assert \false;
  }
  if (a[2] != 0) {
    //@ assert \false;
  }
  if (a[3] != 1) {
    //@ assert \false;
  }
  if (a[4] != 2) {
    //@ assert \false;
  }
  if (a[5] != 0) {
    //@ assert \false;
  }
}
