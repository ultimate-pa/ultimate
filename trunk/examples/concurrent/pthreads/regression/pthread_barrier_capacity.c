//#Unsafe

/*
 * Test that the cast to unsigned is handled properly
 *
 * Date: 2026-10-20
 * Author: schuessf@informatik.uni-freiburg.de
 * 
 */

#include <limits.h>
#include <pthread.h>

int main() {
  long long capacity = UINT_MAX + 2ll;
  pthread_barrier_t barrier;
  pthread_barrier_init(&barrier, NULL, capacity);
  pthread_barrier_wait(&barrier);
  reach_error();
}
