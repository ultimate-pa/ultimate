#include <pthread.h>
#include <stdlib.h>
#include <stdio.h>

extern void __VERIFIER_atomic_begin(void);
extern void __VERIFIER_atomic_end(void);
_Atomic int rw = 0;
static int counter = 0;

void* writer_thread(void* arg) {
    __VERIFIER_atomic_begin();
    if (rw != 0) abort();
    rw = -1;
    __VERIFIER_atomic_end();

    counter = 3;
    counter = 2;

    __VERIFIER_atomic_begin();
    rw = 0;
    __VERIFIER_atomic_end();
    return NULL;
}

void* reader_thread(void* arg) {
    __VERIFIER_atomic_begin();
    if (rw == -1) abort();
    rw += 1;
    __VERIFIER_atomic_end();
 
    int reader_value = counter;
    if (reader_value != counter) {
        abort();
    }

    __VERIFIER_atomic_begin();
    rw -= 1;
    __VERIFIER_atomic_end();
    return NULL;
}

int main(void) {
    pthread_t t_writer, t_reader;
    pthread_create(&t_writer, NULL, writer_thread, NULL);
    pthread_create(&t_reader, NULL, reader_thread, NULL);
    return 0;
}
