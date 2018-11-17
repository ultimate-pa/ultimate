// #Safe
/*
 * Author: Lars Nitzke (lars.nitzke@mailfence.com)
 * Date: 2018-11-17
 * 
 * We check that the main thread will not join thread1 accidentally.
 * 
 */
#include <pthread.h>

typedef unsigned long int pthread_t;

int x;

void *thread1(void *arg) {
  x = 4;
  return 0;
}

void *thread0(void *arg)
{
  pthread_t t1;
  pthread_create(&t1, 0, thread1, 0);
  pthread_join(t1, 0);
  x = 5;
  return 0;
}

int main(void)
{
  pthread_t t0;
  pthread_create(&t0, 0, thread0, 0);
  pthread_join(t0, 0);
  
  if (x == 5) {
    //@ assert \true;
  } else {
    //@ assert \false;
  }  
  return 0;
}