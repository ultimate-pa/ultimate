//#Unsafe
/*
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 18. 10. 2021
 */

typedef unsigned long pthread_t;

#include <stdio.h>

int x;

void* thread1() {
  x = 3; // RACE
  return 0;
}

void* thread2() {
  scanf("%d", &x); // RACE
  return 0;
}

int main() {
  pthread_t t1, t2;
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
