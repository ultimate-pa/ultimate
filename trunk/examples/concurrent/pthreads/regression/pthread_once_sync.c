//#Safe
/*
 * Test that the waiting for pthread_once is modelled correctly.
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2026-10-22
 */

#include <pthread.h>

int x;
pthread_once_t once = PTHREAD_ONCE_INIT;

void init()
{
    x = 42;
}

void *thread(void *n)
{
    pthread_once(&once, init);
    //@ assert x == 42;
    return NULL;
}

int main()
{
    pthread_t t1, t2;
    pthread_create(&t1, NULL, thread, NULL);
    pthread_create(&t2, NULL, thread, NULL);
}
