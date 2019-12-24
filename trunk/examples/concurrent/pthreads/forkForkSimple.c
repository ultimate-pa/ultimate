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
    return 0;
}

void *foo(void *a) {
    pthread_t second_thread;
    pthread_create(&second_thread, NULL, bar, NULL);
    pthread_join(second_thread, NULL);
    return 0;
}

int main() {
    pthread_t thread_id;
    int par = 5;
    pthread_create(&thread_id, NULL, foo, NULL);

//     pthread_join(thread_id, NULL);
    //@assert par == 5;


    return 0;
}
