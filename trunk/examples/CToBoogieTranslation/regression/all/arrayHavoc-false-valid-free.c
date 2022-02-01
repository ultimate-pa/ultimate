/*
 * Testcase added to expose the array havoccing when no initializer is present.
 * author: nutz
 * date: 2015-04-29
 */

#include<stddef.h>
#include<stdio.h>

int main() {
  while (1) {
    int *p, i;
    p = malloc(sizeof(int));
    i = *p;
    int a[4];
    p = a;
    free(p);
    //memory unsafe: the memory alloced for p is not freed but the one for a is freed two times..
  }
  return 0;
}

