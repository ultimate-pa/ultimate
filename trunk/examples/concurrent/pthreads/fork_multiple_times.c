#include <pthread.h>
#include <stdio.h>
#include <assert.h>

typedef unsigned long int pthread_t;


void *foo(void *n) {
    int *x = (int *)n;
    return 0;
}

int main() {

    pthread_t first_thread_id;
    pthread_t second_thread_id;
    pthread_t third_thread_id;

    pthread_create(&first_thread_id, NULL, foo, NULL);
    pthread_create(&second_thread_id, NULL, foo, NULL);
    pthread_create(&third_thread_id, NULL, foo, NULL);

    pthread_join(first_thread_id, NULL);
    pthread_join(second_thread_id, NULL);
    pthread_join(third_thread_id, NULL);

    return 0;
}
