//#Safe
/*
 * Test for memcpy, inspired by strcpy_01.c
 */
#include<string.h>
#include<stdio.h>
int main() {
  char str1[] = { 'a', 'b', 'c' };
  char str2[3];

  memcpy(str2, str1, sizeof(str2));

//  printf("str1: %s\n", str1);
//  printf("str2: %s\n", str2);
//
//  printf("str2[1]: %c\n", str2[1]);
//  printf("str2[3]: %c\n", str2[3]);

  printf("str1[0]: %c\n", str1[0]);
  printf("str2[0]: %c\n", str2[0]);
  printf("str1[1]: %c\n", str1[1]);
  printf("str2[1]: %c\n", str2[1]);
  printf("str1[2]: %c\n", str1[2]);
  printf("str2[2]: %c\n", str2[2]);

  if (str2[0] != 'a') {
    //@ assert \false;
  }
  if (str2[1] != 'b') {
    //@ assert \false;
  }
  if (str2[2] != 'c') {
    //@ assert \false;
  }
}
