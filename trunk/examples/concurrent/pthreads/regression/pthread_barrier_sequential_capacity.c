//#Safe

/*
 * Test that the barrier blocks, if the capacity is big enough
 *
 * Date: 2026-10-20
 * Author: schuessf@informatik.uni-freiburg.de
 */

#include <pthread.h>

int main() {
  pthread_barrier_t barrier;
  int capacity = __VERIFIER_nondet_int();
  if (capacity < 2) return -1;
  pthread_barrier_init(&barrier, NULL, capacity);
  pthread_barrier_wait(&barrier);
  reach_error();
}
