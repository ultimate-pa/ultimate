//#Safe
/*
 * Test behaviour for return in atomic block (implicitly ending the block).
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
int y = 1;

void *foo(void *arg) {
  __VERIFIER_atomic_begin();
  if (y) {
    x = y;
    return (void*) NULL;
  }
  x = 2;
  __VERIFIER_atomic_end();
  return (void*)NULL;
}

int main() {
  pthread_t threadId;
  pthread_create(&threadId, NULL, &foo, NULL);

  y = 0;

  //@ assert x != 0;
}
