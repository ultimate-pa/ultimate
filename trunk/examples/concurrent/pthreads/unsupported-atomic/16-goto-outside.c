//#Safe
/*
 * Test support for GOTO: Leaving the atomic block.
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
  //@ assert x == 0;
  return (void*)NULL;
}

int main() {
  pthread_t threadId;
  pthread_create(&threadId, NULL, & foo, NULL);

  __VERIFIER_atomic_begin();
  x = x + 1;
  if (x != y) {
    goto LABEL;
  }
  x = x - y;
  __VERIFIER_atomic_end();

  // problem: in both cases, control goes through this location (this is the location of "LABEL")
  //          because of the "else" case, this point is marked as atomic end
  //          therefore the atomic block ends here, in both cases!

  LABEL:
  x = 0;
}
