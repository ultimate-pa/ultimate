#include <pthread.h>
#include <stdio.h>
#include <stdbool.h>
#include <assert.h>

typedef unsigned long int pthread_t;


struct int_bool {
    int num;
    bool ret_bool;
};

void *foo(void *n) {
    struct int_bool ret_val;
    int *num = (int *)n;
    if (*num < 10) {
        ret_val.num = *num;
        ret_val.ret_bool = false;
    } else {
        ret_val.num = 9;
        ret_val.ret_bool = true;
    }
    pthread_exit(&ret_val);
}

int main() {

    pthread_t thread_id;
    int x = 1;
    struct int_bool final_value;

    pthread_create(&thread_id, NULL, foo, &x);

    pthread_join(thread_id, (void *)&final_value);
    

    return 0;
}
