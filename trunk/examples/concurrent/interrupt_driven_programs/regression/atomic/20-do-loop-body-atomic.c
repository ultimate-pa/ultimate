//#Safe

#include <pthread.h>
typedef unsigned long int pthread_t;
extern void __VERIFIER_atomic_begin();
extern void __VERIFIER_atomic_end();
extern _Bool __VERIFIER_nondet_bool(void);

int x;

void* thread() {
  do {
    __VERIFIER_atomic_begin();
    x = x + 1;
    x = x - 1;
    __VERIFIER_atomic_end();
  } while (__VERIFIER_nondet_bool());

  return 0;
}

void main() {
  pthread_t t;

  x = 0;
  pthread_create(&t, NULL, thread, NULL);

  //@ assert x == 0;
}
