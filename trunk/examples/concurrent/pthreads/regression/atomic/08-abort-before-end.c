//#Safe
/*
 * Test behaviour for abort in atomic block (implicitly ending the block).
 *
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 2020-01-24
 *
 */

#include <pthread.h>
extern void __VERIFIER_atomic_begin();
extern void __VERIFIER_atomic_end();

typedef unsigned long int pthread_t;
int x = 1;
int y = 0;

void *foo(void *arg) {
  __VERIFIER_atomic_begin();
  if (y == 0) {
    x = y;
    abort();
  }
  x = 2;
  __VERIFIER_atomic_end();
  return (void*)NULL;
}

int main() {
  pthread_t threadId;
  pthread_create(&threadId, NULL, &foo, NULL);

  y = 1;

  //@ assert x != 0;
}
