#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

typedef unsigned long int pthread_t;
 
// One global variable - changes in threads.
int g = 0;
 
// The function to be executed by all threads
void *myThread(void *vargp)
{
    int *myid = (int *)vargp; 
    static int s = 0;
    ++s; ++g;
 
    printf("Thread ID: %d, Static: %d, Global: %d\n", *myid, ++s, ++g);
}
 
int main()
{
    int i;
    pthread_t tid;
 
    // Create 3 threads.
    for (i = 0; i < 3; i++)
        pthread_create(&tid, NULL, myThread, (void *)&i);
 
    pthread_join(tid, NULL);
    return 0;
}
