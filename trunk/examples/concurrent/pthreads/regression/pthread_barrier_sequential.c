//#Unsafe

/*
 * Test that the barrier also works for a single thread and returns
 * PTHREAD_BARRIER_SERIAL_THREAD
 *
 * Date: 2026-10-20
 * Author: schuessf@informatik.uni-freiburg.de
 */

#include <pthread.h>

int main() {
  pthread_barrier_t barrier;
  pthread_barrier_init(&barrier, NULL, 1);
  int ret = pthread_barrier_wait(&barrier);
  if (ret == PTHREAD_BARRIER_SERIAL_THREAD) reach_error();
}
