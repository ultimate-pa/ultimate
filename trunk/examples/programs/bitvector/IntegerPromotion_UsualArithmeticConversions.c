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

int main() {
  
  /* times */
  if (sizeof(char) == 1 && sizeof(int) > 1) {
    unsigned char a = 16;
    unsigned char b = 16;
    int c = a * b;
    printf("%d\n", c);
    if (c != 256) {
        //@ assert(\false);
    }
  }
  
  /* division */
  if (sizeof(char) == 1 && sizeof(int) > 1) {
    unsigned char a = 32;
    signed char b = -13;
    int c = a / b;
    printf("%d\n", c);
    if (c != -2) {
        //@ assert(\false);
    }
  }

  /* modulo */
  if (sizeof(char) == 1 && sizeof(int) > 1) {
    unsigned char a = 32;
    signed char b = -13;
    int c = a % b;
    printf("%d\n", c);
    if (c != 6) {
        //@ assert(\false);
    }
  }

  /* plus */
  if (sizeof(char) == 1 && sizeof(int) > 1) {
    unsigned char a = 128;
    unsigned char b = 128;
    int c = a + b;
    printf("%d\n", c);
    if (c != 256) {
        //@ assert(\false);
    }
  }
  
  /* minus */
  if (sizeof(char) == 1 && sizeof(int) > 1) {
    unsigned char a = 7;
    unsigned char b = 13;
    int c = a - b;
    printf("%d\n", c);
    if (c != -6) {
        //@ assert(\false);
    }
  }

  /* relational */
  if (sizeof(char) == 1 && sizeof(int) > 1) {
    unsigned char a = 1;
    signed char b = -1;
    if (a < b) {
        //@ assert(\false);
    } else {
        printf("not less\n");
    }
  }


  /* equals */
  if (sizeof(char) == 1 && sizeof(int) > 1) {
    unsigned char a = 255;
    signed char b = -1;
    if (a == b) {
        //@ assert(\false);
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
        //@ assert(\false);
    }
  }

  /* bitwise XOR */
  if (sizeof(char) == 1 && sizeof(int) > 1) {
    unsigned char a = 255;
    signed char b = -1;
    int c = a ^ b;
    printf("%d\n", c);
    if (c != -256) {
        //@ assert(\false);
    }
  }
    
  /* conditional operator */
  if (sizeof(char) == 1 && sizeof(int) > 1) {
    unsigned char a = 13;
    signed char b = -1;
    int c = (0 ? a : b);
    printf("%d\n", -1);
    if (c != -1) {
        //@ assert(\false);
    }
  }
}
