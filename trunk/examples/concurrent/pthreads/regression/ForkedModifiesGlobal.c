//#Safe
/* 
 * Reproduce bug that modifies clause was not transitive.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2018-10-23
 * 
 */

#include <stdlib.h>
#include <pthread.h>

typedef unsigned long int pthread_t;
 
int g = 0;
 
void *myThread(void *vargp)
{
	++g;
}
 
int main()
{
    int i;
    pthread_t tid;
// 	myThread((void *)&i);
    pthread_create(&tid, NULL, myThread, (void *)&i);
    return 0;
}
