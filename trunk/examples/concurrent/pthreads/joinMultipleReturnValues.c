//#Safe
/*
 * Author: Lars Nitzke, 
 *         Matthias Heizmann (heizmann@informatik.uni-freiburg.de),
 *         Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: Spring 2019
 */
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

typedef unsigned long int pthread_t;


struct int_bool {
    int num;
    _Bool ret_bool;
};

void *foo(void *n) {
    struct int_bool* ret_val = malloc(sizeof(struct int_bool));
    int *num = (int *)n;
    if (*num < 10) {
        ret_val->num = *num;
        ret_val->ret_bool = 0;
    } else {
        ret_val->num = 9;
        ret_val->ret_bool = 1;
    }
    pthread_exit(ret_val);
}

int main() {

    pthread_t thread_id;
    int x = 1;
    struct int_bool* final_value;

    pthread_create(&thread_id, NULL, foo, &x);
    pthread_join(thread_id, (void*)&final_value);

    int num = final_value->num;
    _Bool ret = final_value->ret_bool;
    //@ assert num == 1;
    //@ assert ret == 0;

    return 0;
}
