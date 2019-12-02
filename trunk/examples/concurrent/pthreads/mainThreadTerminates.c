//#Unsafe
/*
 * Author: Lars Nitzke (lars.nitzke@mailfence.com)
 * Date: 2019-02-01
 * 
 * When the main thread terminates, all other threads created in the process will be terminated 
 * as well.
 * But can we guarantee that we never reach the line 21 here?
 * 
 */

#include <pthread.h>
#include <stdio.h>

typedef unsigned long int pthread_t;

void *worker_thread(void *arg) {
    int x = 0;
    while (x < 100) {
        x++;
    }
    //@ assert 1 == 2;
}

int main() {
    pthread_t thread;
    pthread_create(&thread, NULL, worker_thread, NULL);
}
