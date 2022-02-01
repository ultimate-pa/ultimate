//#Unsafe
/*
 * Test behaviour for atomic block end without begin.
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
  x = 2;
  return (void*)NULL;
}

int main() {
  pthread_t threadId;
  pthread_create(&threadId, NULL, &foo, NULL);

  x = 1;
  x = x + 1;
  __VERIFIER_atomic_end();

  //@ assert x != 3;
}
