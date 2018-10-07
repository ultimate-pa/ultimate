/**
 * Author: Lars Nitzke (lars.nitzke@outlook.com)
 * Date: 2018-09-28
 */

#include <pthread.h>
#include <stdio.h>
#include <assert.h>
#include <stdbool.h>

typedef unsigned long int pthread_t;

int x;

void *firstIncrement() {
    int localx;
    int i = 0;
    while (i < 5) {
        localx = x;
        x = localx + 1;
        i++;
    }
}

void *secondIncrement() {
    int localx;
    int i = 0;
    while (i < 5) {
        localx = x;
        x = localx +1;
        i++;
    }
}

int main() {
    pthread_t first_increment_id;
    pthread_t second_increment_id;
    bool y;
    x = 0;

    pthread_create(&first_increment_id, NULL, firstIncrement, NULL);
    pthread_create(&second_increment_id, NULL, secondIncrement, NULL);

    pthread_join(first_increment_id, NULL);
    pthread_join(second_increment_id, NULL);
    
    assert(x >= 2);
    return 0;
}
