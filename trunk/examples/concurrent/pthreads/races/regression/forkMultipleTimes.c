//#Unsafe
/*
 * Author: Lars Nitzke, 
 *         Matthias Heizmann (heizmann@informatik.uni-freiburg.de),
 *         Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: Spring 2019
 */
#include <pthread.h>
#include <stdio.h>

typedef unsigned long int pthread_t;

int counter = 0;

void *foo(void *n) {
    int *x = (int *)n;
    *x = ++counter;
    return 0;
}

int main() {

    int val = 0;

    pthread_t first_thread_id;
    pthread_t second_thread_id;

    pthread_create(&first_thread_id, NULL, foo, &val);
    pthread_create(&second_thread_id, NULL, foo, &val);

    pthread_join(first_thread_id, NULL);
    pthread_join(second_thread_id, NULL);

    return 0;
}
