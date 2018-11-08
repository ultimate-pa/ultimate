//#Unsafe
/* 
 * Little unsave example for the pthread_exit function.
 * 
 * Author: lars.nitzke@mailfence.com
 * Date: 2018-11-08
 * 
 */
#include <pthread.h>
#include <stdio.h>

typedef unsigned long int pthread_t;

void *foo(void *n) {    
    int *ret = (int *)n;
	(*ret)--;
    pthread_exit(NULL);
}

int main() {
    pthread_t th_id;
    int x = 1;
    pthread_create(&th_id, NULL, foo, &x);
    pthread_join(th_id, NULL);
    printf("This line is reachable\n");
    //@ assert \false;
    return 0;
}
