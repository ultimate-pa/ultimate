//#Unsafe
/*
 * Author: Dominik Klumpp
 * Date: August 10 2021
 *
 * Tests an optimization that creates thread IDs with different types during C translation. This allows to statically
 * match join statements to their corresponding fork statement. Here we reduce the number of JoinThreadOtherTransitions
 * from 10*10 to 10, thereby drastically simplifying verification.
 */

#include <pthread.h>
typedef unsigned long int pthread_t;

void *thread(void * arg)
{
  return arg;
}

int main()
{
  pthread_t t0, t1, t2, t3, t4, t5, t6, t7, t8, t9;

  goto forks;

  joins:
  void* result;
  pthread_join(t0, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  pthread_join(t3, 0);
  pthread_join(t4, 0);
  pthread_join(t5, 0);
  pthread_join(t6, 0);
  pthread_join(t7, 0);
  pthread_join(t8, 0);
  pthread_join(t9, &result);
  //@ assert result != 9;

  return 0;

  forks:
  pthread_create(&t0, 0, thread, (void*)0);
  pthread_create(&t1, 0, thread, (void*)1);
  pthread_create(&t2, 0, thread, (void*)2);
  pthread_create(&t3, 0, thread, (void*)3);
  pthread_create(&t4, 0, thread, (void*)4);
  pthread_create(&t5, 0, thread, (void*)5);
  pthread_create(&t6, 0, thread, (void*)6);
  pthread_create(&t7, 0, thread, (void*)7);
  pthread_create(&t8, 0, thread, (void*)8);
  pthread_create(&t9, 0, thread, (void*)9);

  goto joins;
}
