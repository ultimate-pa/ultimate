//#Safe
// Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
// Date: 2021-11-01

#include <stdlib.h>
#include <stdio.h>
#include <stddef.h>
#include <stdint.h>

int main() {
  size_t max = 18446744073709551615UL;

  if (max <= 0) {
    printf("ERROR\n");
    //@ assert 0;
  } else {
    printf("SAFE\n");
  }
}
