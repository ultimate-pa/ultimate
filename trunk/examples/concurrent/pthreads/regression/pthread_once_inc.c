//#Safe
/*
 * Test that the initializer for pthread_once is only executed once.
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2026-10-22
 */

#include <pthread.h>

int x;
pthread_once_t once = PTHREAD_ONCE_INIT;

void init() {
  x++;
}

void *thread(void *n) {
  pthread_once(&once, init);
  return NULL;
}

int main() {
  pthread_t t;
  pthread_create(&t, NULL, thread, NULL);
  pthread_once(&once, init);
  //@ assert x == 1;
}
