//#Safe

#include <pthread.h>
extern void __VERIFIER_atomic_begin();
extern void __VERIFIER_atomic_end();

typedef unsigned long int pthread_t;
int x = 1;
int y = 1;
int z = 1;

void *foo(void *arg) {
  __VERIFIER_atomic_begin();
  x = x > 0 ? x : -x;
  y = y > 0 ? y : -y;
  z = x > y ? x - y : (y > x ? y - x : 0);
  x = x + 1;
  if (x < z) {
    z = 0;
    __VERIFIER_atomic_end();
    y = 5;
  } else {
    z = 1;
    __VERIFIER_atomic_end();
    y = 7;
  }
  return (void*)NULL;
}

int main() {
  pthread_t threadId;
  pthread_create(&threadId, NULL, &foo, NULL);

  y = 0;

  //@ assert z >= 0;
}
