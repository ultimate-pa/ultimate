// #Safe
/*
 * Test that pthread_join takes into account the thread ID.
 * Assertion cannot fail because even if the 2nd thread (dec) executes between assignment of y and the assertion,
 * The assertion remains valid. If on the other hand the 1st thread (inc) were to execute, the assertion would fail.
 *
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: Spring 2020
 */
#include <pthread.h>
#include <stdio.h>

typedef unsigned long int pthread_t;
int x = 0;


void *inc(void *n) {
    x++;
    return NULL;
}

void *dec(void *n) {
    x--;
    return NULL;
}

int main() {
    pthread_t first_th_id;
    pthread_t second_th_id;

    pthread_create(&first_th_id, NULL, inc, NULL);
    pthread_create(&second_th_id, NULL, dec, NULL);

    pthread_join(first_th_id, NULL);
    int y = x;

    //@ assert x <= y;
    
    return 0;
}
