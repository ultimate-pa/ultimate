#include <stdio.h>
#include <pthread.h>
#include <stdlib.h>

typedef unsigned long int pthread_t;

void *worker_thread(void *arg) {
        return (void*)792;
}

int main() {
        int i;
        pthread_t thread;
        pthread_create(&thread, NULL, worker_thread, NULL);
        pthread_join(thread, (void **)&i);
}
