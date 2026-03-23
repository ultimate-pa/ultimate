//#Safe
/*
 * Check if we correctly support the __VERIFIER_atomic_* functions from the SV-COMP.
 *
 * Authors: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
            Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 2020-01-24
 *
 */

#include <pthread.h>

typedef unsigned long int pthread_t;
int g = 0;

void *foo(void *arg) {
  g = g * 2;
  return (void*)NULL;
}

void __VERIFIER_atomic_modify() {
  g = g + 1;
  g = g - 1;
}

int main() {
  pthread_t threadId;
  pthread_create(&threadId, NULL, & foo, NULL);

  __VERIFIER_atomic_modify();

  if (g > 0) {
    //@ assert \false;
  }		
}
