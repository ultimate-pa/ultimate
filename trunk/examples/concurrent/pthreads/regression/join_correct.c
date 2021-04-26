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

void* increment(void *arg)
{
  return (void*) (((int)arg) + 42);
}

void main(void)
{
  pthread_t threads[2];
  int x = 0;

  while (x < 2) {
    pthread_create(&threads[x], NULL, increment, (void*)x);
    x++;
  }

  void* result;
  pthread_join(threads[0], &result);
  //@ assert result == 42;
}

