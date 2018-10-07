#include <pthread.h>
#include <stdio.h>
#include <assert.h>

typedef unsigned long int pthread_t;


void *add(void *n) {
    int *numbers = (int *)n;
    int result = numbers[0] + numbers[1];
    return (void *)result;
}

int main() {
    int numbers[2] = {1, 2};

    pthread_t thread_id;

    void *ret;

    pthread_create(&thread_id, NULL, add, (void*)numbers);
    pthread_join(thread_id, &ret);

    assert((int)ret == 3);

    return 0;
}
