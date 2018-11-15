//#Safe
/*
 * Test for memcpy, inspired by strcpy_01.c
 */
#include<string.h>
#include<stdio.h>
int main() {
  short a[10] = { 1, 0 };

  //memcpy(a + (3* sizeof(short)), a, 3 * sizeof(short));
  memcpy(a + 1, a, 1);

  printf("a[0]: %hi\n", a[0]);
  printf("a[1]: %hi\n", a[1]);

  if (a[0] != 1) {
    //@ assert \false;
  }
  if (a[1] != 1) {
    //@ assert \false;
  }
}
