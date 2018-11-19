//#Unsafe
/*
 * Test compound literals (e.g. "(int) { -1 }", see also C11 6.5.2.5).
 *
 * constant compound literals may share memory (like string literals)
 */
#include<stdio.h>
int main() {
  int * p = & (const int) { -1 };
  int * q = & (const int) { -1 };
  printf("res: %d\n", p == q);
  //@ assert p != q;
}
