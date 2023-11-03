//#Safe
/*
 * Author: Lars Nitzke, 
 *         Matthias Heizmann (heizmann@informatik.uni-freiburg.de),
 *         Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: Spring 2019
 */
#include <pthread.h>
#include <stdio.h>

typedef unsigned long int pthread_t;


void *bar(void *b) {
    int *c = (int *)b;

    // Parameter is correctly passed
    int val = *c;
    //@ assert val == 5;

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

    // Result is correctly passed
    int ret = *x;
    //@ assert ret == 10;
    printf("%u\n",ret);

    // Side-effect is captured
    // assert par == 10; // commented out, as (surprisingly) this takes a lot longer

    return 0;
}
