/*
 * Testcase to expose malloccing behaviour when an onHeap variable is passed to a function
 * author: nutz
 * date: 2015-04-29
 */

#include<stddef.h>
#include<stdio.h>

int f(int i) {
  int *j = &i;
  return *j;
}

int main() {
  int i;
  f(i);
  return 0;
}



