#include <pthread.h>
#include <stdio.h>
#include <assert.h>

typedef unsigned long int pthread_t;


int globVar;

void *increment(void *n) {
    printf("&n : %d\n", &n);
    int *result = (int *)n;
    (*result)++;
    printf("result : %d\n", result);
    printf("*result : %d\n", *result);
    printf("&result : %d\n", &result);
    return (void *)result;
}

int main() {
    int locVar = 7;
    globVar = 0;

    pthread_t thread_id;

    pthread_create(&thread_id, NULL, increment, &globVar);
    assert(globVar == 0);
    assert(locVar == 7);
    pthread_join(thread_id, NULL);
    assert(globVar == 0);
    assert(locVar == 7);

    return 0;
}
