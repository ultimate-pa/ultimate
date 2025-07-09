#include <pthread.h>
#include <stdlib.h>

extern void __VERIFIER_atomic_begin(void);
extern void __VERIFIER_atomic_end(void);
extern void abort(void);

int counter = 0;
_Atomic bool mutex = false;

void* thread1(void* arg) {
    __VERIFIER_atomic_begin();
    if (mutex) abort();
    mutex = true;
    __VERIFIER_atomic_end();

    counter = 1;

    __VERIFIER_atomic_begin();
    mutex = false;
    __VERIFIER_atomic_end();
    return NULL;
}

void* thread2(void* arg) {
    __VERIFIER_atomic_begin();
    if (mutex) abort();
    mutex = true;
    __VERIFIER_atomic_end();

    counter = 2;

    __VERIFIER_atomic_begin();
    mutex = false;
    __VERIFIER_atomic_end();
    return NULL;
}

int main() {
    pthread_t t1, t2;
    pthread_create(&t1, NULL, thread1, NULL);
    pthread_create(&t2, NULL, thread2, NULL);
    return 0;
}


