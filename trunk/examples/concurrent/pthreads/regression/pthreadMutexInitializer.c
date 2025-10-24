//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2025-05-08
 */

#include <pthread.h>

pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

int main() {
  int ret = pthread_mutex_lock(&mutex);
  //@ assert ret == 0;
  return 0;
}
