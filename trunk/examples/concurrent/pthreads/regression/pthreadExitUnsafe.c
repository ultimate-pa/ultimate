//#Unsafe
/* 
 * Author: lars.nitzke@mailfence.com
 * Date: 2018-11-08
 * 
 * We check if pthread_exit really terminates the process and it does not ignore the pthread_exit statement.
 * Unsafe, because the assertion in line 28 fails if pthread_exit terminates the process.
 * 
 */
#include <pthread.h>
#include <stdio.h>
#include <stdbool.h>

typedef unsigned long int pthread_t;

void *foo(void *n) {
    while (1) {
        pthread_exit(NULL);
        //@ assert \true;
    }
}

int main() {
    pthread_t th_id;
    pthread_create(&th_id, NULL, foo, NULL);
    pthread_join(th_id, NULL);
    printf("This line is reachable\n");
    //@ assert \false;
    return 0;
}
