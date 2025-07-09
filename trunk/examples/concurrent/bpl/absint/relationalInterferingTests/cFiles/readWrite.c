#include <pthread.h>
#include <stdlib.h>
#include <stdio.h>

static pthread_rwlock_t rwlock = PTHREAD_RWLOCK_INITIALIZER;
static int counter = 0;
static int reader_value = 0;

void* writer_thread(void* arg) {
    pthread_rwlock_wrlock(&rwlock);
    counter += 3;
    pthread_rwlock_unlock(&rwlock);
    return NULL;
}

void* reader_thread(void* arg) {
    pthread_rwlock_rdlock(&rwlock);
    reader_value = counter;
    if (reader_value != counter) {
        abort();
    }
    pthread_rwlock_unlock(&rwlock);
    return NULL;
}

int main(void) {
    pthread_t t_writer, t_reader;
    pthread_create(&t_writer, NULL, writer_thread, NULL);
    pthread_create(&t_reader, NULL, reader_thread, NULL);
    pthread_rwlock_destroy(&rwlock);
    printf("%d %d PTHREAD\n", counter, reader_value);
    return 0;
}

