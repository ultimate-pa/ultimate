//#Safe
/*
 * TODO 2019-12-02: I do not understand the purpose of this
 * example. Does it check for a violation of memory safety
 * (status not allocated) or is the intention to check something
 * different and we should have two different copies of this
 * example.
 * 
 * Author: Lars Nitzke,
           Matthias Heizmann (heizmann@informatik.uni-freiburg.de),
 *         Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: Spring 2019
 * 
 */
#include <pthread.h>
#include <stdio.h>

typedef unsigned long int pthread_t;

void *myThread()
{
    return (void *) 42;
}

int main()
{
   pthread_t tid;
   void *status;
   pthread_create(&tid, NULL, myThread, NULL);
   pthread_join(tid, &status);
   //@ assert status == 42;

   return 0;
}
