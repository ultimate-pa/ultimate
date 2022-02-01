//#Safe
/*
 * Test compound literals (e.g. "(int) { -1 }", see also C11 6.5.2.5).
 */
#include<stdio.h>
int main() {
  int * p = & (int) { -1 };
  int * q = & (int) { -1 };
  printf("res: %d\n", p == q);
  // because the compound literals are not constant they may not share memory
  //@ assert p != q;
}
