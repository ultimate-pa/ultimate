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


void *add(void *n) {
    int *numbers = (int *)n;
    int result = numbers[0] + numbers[1];
    return (void *)result;
}

int main() {
    int numbers[2] = {1, 2};

    pthread_t thread_id;
    pthread_create(&thread_id, NULL, add, (void*)numbers);

    void *ret_val;
    pthread_join(thread_id, &ret_val);

    // Correct result is computed and returned
    int x = (int)ret_val;
    //@ assert x == 3;

    return 0;
}
