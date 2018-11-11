//#Safe
/* 
 * Little example to represent pthread_exit function.
 * 
 * Author: lars.nitzke@mailfence.com
 * Date: 2018-11-08
 * 
 */
#include <pthread.h>
#include <stdio.h>

typedef unsigned long int pthread_t;

void *dec(void *n) {
    
    int *ret = (int *)n;
	(*ret)--;
    pthread_exit((void *)ret);
    //@ assert \false;
}

int main() {
    pthread_t th_id;
    int x = 1;
    pthread_create(&th_id, NULL, dec, &x);
    void *y;
    pthread_join(th_id, &y);
    int z = *(int *)y;
    //@ assert z == 0;
    return 0;
}