//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2025-04-30
 */

#include <stdatomic.h>
#include <pthread.h>

atomic_int x;
atomic_ulong y;
atomic_char z;

void* thread1() {
  x = 1;
  y = 1;
  z = 1;
}

void* thread2() {
  x = 2;
  y = 2;
  z = 2;
}

int main() {
  pthread_t t1, t2;
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
