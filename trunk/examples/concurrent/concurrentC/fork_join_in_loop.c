#include <pthread.h>
#include <stdio.h>

void *foo(void *i) {
    int y = 4;
}

int main() {
    pthread_t thread_id;

    int x = 1;

    while (x < 3) {
        pthread_create(&thread_id, NULL, foo, &x);
        printf("Successfully forked thread %d\n", x);
        pthread_join(thread_id, NULL);
        printf("Successfully joined thread %d\n", x);
        x++;
    }

    return 0;
}