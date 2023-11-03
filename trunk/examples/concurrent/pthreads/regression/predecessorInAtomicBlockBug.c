//#Unsafe
/*
 * Bug: we incorrectly add the predecessor statement of 
 * __VERIFIER_atomic_begin(); to the atomic block.
 * 
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2020-01-25
 *
 */

#include <pthread.h>
extern void __VERIFIER_atomic_begin();
extern void __VERIFIER_atomic_end();

typedef unsigned long int pthread_t;
int x = 0;

void *foo(void *arg) {
  //@ assert x == 0;
  return (void*)NULL;
}

int main() {
  pthread_t threadId;
  pthread_create(&threadId, NULL, & foo, NULL);

  x = x - 1;
  __VERIFIER_atomic_begin();
  x = x + 1;
  __VERIFIER_atomic_end();
}
