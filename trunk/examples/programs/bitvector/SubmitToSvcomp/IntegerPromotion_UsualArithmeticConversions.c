//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-08-26
 * 
 * Test if the integer promotions were done as the first step of the usual
 * arithmetic conversions.
 * If every single assert fails if integer promotions are not done.
 */

#include <stdio.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int main() {
  
  /* times */
  if (sizeof(char) == 1 && sizeof(int) > 1) {
    unsigned char a = 16;
    unsigned char b = 16;
    int c = a * b;
    printf("%d\n", c);
    if (c != 256) {
        __VERIFIER_error();
    }
  }
  
  /* division */
  if (sizeof(char) == 1 && sizeof(int) > 1) {
    unsigned char a = 32;
    signed char b = -13;
    int c = a / b;
    printf("%d\n", c);
    if (c != -2) {
        __VERIFIER_error();
    }
  }

  /* modulo */
  if (sizeof(char) == 1 && sizeof(int) > 1) {
    unsigned char a = 32;
    signed char b = -13;
    int c = a % b;
    printf("%d\n", c);
    if (c != 6) {
        __VERIFIER_error();
    }
  }

  /* plus */
  if (sizeof(char) == 1 && sizeof(int) > 1) {
    unsigned char a = 128;
    unsigned char b = 128;
    int c = a + b;
    printf("%d\n", c);
    if (c != 256) {
        __VERIFIER_error();
    }
  }
  
  /* minus */
  if (sizeof(char) == 1 && sizeof(int) > 1) {
    unsigned char a = 7;
    unsigned char b = 13;
    int c = a - b;
    printf("%d\n", c);
    if (c != -6) {
        __VERIFIER_error();
    }
  }

  /* relational */
  if (sizeof(char) == 1 && sizeof(int) > 1) {
    unsigned char a = 1;
    signed char b = -1;
    if (a < b) {
        __VERIFIER_error();
    } else {
        printf("not less\n");
    }
  }


  /* equals */
  if (sizeof(char) == 1 && sizeof(int) > 1) {
    unsigned char a = 255;
    signed char b = -1;
    if (a == b) {
        __VERIFIER_error();
    } else {
        printf("not equal\n");
    }
  }

  /* bitwise OR */
  if (sizeof(char) == 1 && sizeof(int) > 1) {
    unsigned char a = 255;
    signed char b = -1;
    int c = a | b;
    printf("%d\n", c);
    if (c != -1) {
       __VERIFIER_error();
    }
  }

  /* bitwise XOR */
  if (sizeof(char) == 1 && sizeof(int) > 1) {
    unsigned char a = 255;
    signed char b = -1;
    int c = a ^ b;
    printf("%d\n", c);
    if (c != -256) {
        __VERIFIER_error();
    }
  }
    
  /* conditional operator */
  if (sizeof(char) == 1 && sizeof(int) > 1) {
    unsigned char a = 13;
    signed char b = -1;
    int c = (0 ? a : b);
    printf("%d\n", -1);
    if (c != -1) {
        __VERIFIER_error();
    }
  }
}
