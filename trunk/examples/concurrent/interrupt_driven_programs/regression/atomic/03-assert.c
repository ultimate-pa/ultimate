//#Safe
/*
 * Check support for assertions in atomic blocks.
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

void *foo(void *arg) {
  x = 0;
  return (void*)NULL;
}

void __VERIFIER_atomic_check() {
  x = 1;
  //@ assert x;
  x = 0;
}

int main() {
  pthread_t threadId;
  pthread_create(&threadId, NULL, &foo, NULL);

  __VERIFIER_atomic_begin();
  x = 1;
  //@ assert x;
  x = 0;
  __VERIFIER_atomic_end();

  __VERIFIER_atomic_check();
}
