#include <pthread.h>
#include <stdio.h>

void *bar(void *b) {
    int *c = (int *)b;
    printf("c* = %d\n", *c);
    *c += 5;
    return (void *)c;
}

void *foo(void *a) {
    pthread_t second_thread;
    int *param = (int *)a;
    void *ret;
    pthread_create(&second_thread, NULL, bar, param);
    pthread_join(second_thread, &ret);
    return ret;
}

int main() {
    pthread_t thread_id;
    int par = 5;
    pthread_create(&thread_id, NULL, foo, &par);

    void *ret_val;
    pthread_join(thread_id, &ret_val);
    int *x = (int *)ret_val;

    printf("Returned value: %d\n", *x);

    return 0;
}