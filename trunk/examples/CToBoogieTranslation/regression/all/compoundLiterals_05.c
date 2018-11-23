//#Safe
/*
 * Test compound literals (e.g. "(int) { -1 }", see also C11 6.5.2.5).
 */
#include<stdio.h>
int x = 0;

int bar() {
  x--;
  return (int) { x };
}

int main() {
  int res;
  res = bar();
  printf("res: %d\n", res);
  //@ assert res == -1;
  res = bar();
  printf("res: %d\n", res);
  //@ assert res == -2;
}
