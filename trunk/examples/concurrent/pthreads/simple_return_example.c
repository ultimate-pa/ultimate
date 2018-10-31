#include <pthread.h>
#include <stdio.h>

typedef unsigned long int pthread_t;


void *bar(void *b) {
    int *c = (int *)b;
    *c += 5;
    return (void *)c;
}

int main() {
    pthread_t thread_id;
    int par = 5;
    pthread_create(&thread_id, NULL, bar, &par);

    void *ret_val;
    pthread_join(thread_id, &ret_val);
    int *x = (int *)ret_val;

    //@ assert x == 10;
    return 0;
}