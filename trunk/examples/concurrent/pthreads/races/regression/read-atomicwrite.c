//#Unsafe
/*
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 18. 10. 2021
 */

// The write is atomic, the read is not.

extern void __VERIFIER_atomic_begin();
extern void __VERIFIER_atomic_end();

typedef unsigned long pthread_t;

unsigned int x;

void* thread1() {
  __VERIFIER_atomic_begin();
  x = 0u-1; // RACE
  __VERIFIER_atomic_end();
  return 0;
}

void* thread2() {
  if (x != 0xFFFFFF) { // RACE
    return 0;
  }
  return 1;
}

int main() {
  pthread_t t1, t2;
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
}
