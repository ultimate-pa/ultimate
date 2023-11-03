//#Safe
/*
 * Test behaviour for atomic block containing loops (unsupported).
 *
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 2020-01-24
 *
 */

#include <pthread.h>
extern void __VERIFIER_atomic_begin();
extern void __VERIFIER_atomic_end();

typedef unsigned long int pthread_t;
int x = 0;
int y;

void *foo(void *arg) {
  x = -1;
  return (void*)NULL;
}

int main() {
  pthread_t threadId;
  pthread_create(&threadId, NULL, &foo, NULL);

  __VERIFIER_atomic_begin();
  x = 0;
  while (x < y) {
    x++;
  }
  __VERIFIER_atomic_end();

  //@ assert x < 0 || x == y;
}
