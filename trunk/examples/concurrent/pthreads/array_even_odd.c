//#Safe
// Author: Dennis Wölfing

#include <pthread.h>

typedef unsigned long int pthread_t;

// Increasing this number increases the time needed for verification.
const int size = 10;
int* a;
int i;
int j;

void* foo(void* p) {
    int x;
    while (i < size) {
        a[i] = 0;
        x = a[i];
        //@ assert x == 0;
        i += 2;
    }
}

void* bar(void* p) {
    int x;
    while (j < size) {
        a[j] = 1;
        x = a[j];
        //@ assert x == 1;
        j += 2;
    }
}

int main() {
    a = malloc(size);

    i = 0;
    j = 1;

    pthread_t first_thread_id;
    pthread_t second_thread_id;

    pthread_create(&first_thread_id, NULL, foo, NULL);
    pthread_create(&second_thread_id, NULL, bar, NULL);

    return 0;
}
