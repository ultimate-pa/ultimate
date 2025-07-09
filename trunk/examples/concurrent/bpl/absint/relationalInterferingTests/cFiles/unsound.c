extern void __VERIFIER_atomic_begin(void);
extern void __VERIFIER_atomic_end(void);
extern void abort(void);

int counter = 0;
int mutex = 0;

void* thread_func(void* arg) {
    __VERIFIER_atomic_begin();
    if (mutex) abort();
    mutex = 1;
    __VERIFIER_atomic_end();

    counter++;

    __VERIFIER_atomic_begin();
    mutex = 0;
    __VERIFIER_atomic_end();

    return 0;
}

int main() {
    // Call thread_func twice manually (no actual threads)
    thread_func(0);
    thread_func(0);

    return 0;
}

