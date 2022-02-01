//#Safe
/*  
 * Author: lars.nitzke@mailfence.com
 * Date: 2018-11-08
 * 
 * We check that pthread_exit returns the correct value.
 * Safe because it should be subtract 1 from x which is one. So z should be 0;
 * 
 */
#include <pthread.h>
#include <stdio.h>

typedef unsigned long int pthread_t;

void *dec(void *n) {
    
    int *ret = (int *)n;
	(*ret)--;
    pthread_exit((void *)ret);
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