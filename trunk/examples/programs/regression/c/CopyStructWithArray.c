//#Safe
/*
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 10. 11. 2021
 *
 * C translation bug: While copying the struct, the values of y.arr were read from the base address of x.
 * As a result, y.arr[0] actually contained the value of x.field1, i.e., 12.
 */

#include <stdio.h>

typedef unsigned long pthread_t;

struct MYSTRUCT {
  int field1;
  int field2;
  int field3;
  int arr[2];
};

struct MYSTRUCT x, y; // all initialized to 0

int main() {
  x.field1 = 12;
  y = x;

  int z = y.arr[0];
  printf("Equal: 0 == %d\n", z);
  //@ assert z == 0;
}
