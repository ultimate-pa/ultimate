#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int main() {
    int* x = alloca(sizeof(int));
    int* y = alloca(sizeof(int));
    int* d = alloca(sizeof(int));
    
    while (*x > 0 && *y > 0 && *d > 0) {
        if (__VERIFIER_nondet_int()) {
            *x = *x - 1;
            *d = __VERIFIER_nondet_int();
        } else {
            *x = __VERIFIER_nondet_int();
            *y = *y - 1;
            *d = *d - 1;
        }
    }
}