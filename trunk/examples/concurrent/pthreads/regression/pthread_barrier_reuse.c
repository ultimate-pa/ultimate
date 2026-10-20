//#Safe

/*
 * Test that synchronising also works when the barriers are reused
 *
 * Date: 2026-10-20
 * Author: schuessf@informatik.uni-freiburg.de
 */

#include <pthread.h>

pthread_barrier_t barrier;
int x = 0;
int y = 0;

void* thread1(void* ptr) {
  while (x < 3) {
    pthread_barrier_wait(&barrier);
    x++;
    if (x < y) reach_error();
  }
  return NULL;
}

void* thread2(void* ptr) {
  while (y < 3) {
    pthread_barrier_wait(&barrier);
    y++;
  }
  return NULL;
}


int main() {
  pthread_barrier_init(&barrier, NULL, 2);
  pthread_t t1, t2;
  pthread_create(&t1, NULL, thread1, NULL);
  pthread_create(&t2, NULL, thread2, NULL);
}
