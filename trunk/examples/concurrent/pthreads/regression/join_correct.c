// #Safe
/*
 * Author: Dominik Klumpp
 * Date: April 17 2021
 *
 * Test that a pthread_join actually joins the correct thread instance, even if multiple thread instances were created by the same pthread_create statement.
 * A bug in ULTIMATE allowed the wrong instance to be joined, leading to unsoundness.
 *
 * The reason was that the ID of the created thread was always the same for all executions of a pthread_create statement.
 * The solution is to instead maintain and increment a global counter.
 */
#include <pthread.h>

typedef unsigned long int pthread_t;
int ret[2];

void* thread0(void *arg)
{
  int in = *((int*)arg);
  ret[in] = in - 1;
  return (void*) &ret[in];
}

void main(void)
{
  pthread_t threads[2];
  int x = 0;

  while (x < 2) {
    pthread_create(&threads[x], NULL, thread0, &x);
    x++;
  }
  pthread_join(threads[0], &x);

  //@ assert x == -1;
}

