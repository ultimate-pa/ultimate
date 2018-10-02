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

   printf("%d",(int)status);   

   return 0;
}
