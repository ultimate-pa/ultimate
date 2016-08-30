#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int main() {
    int* x = alloca(sizeof(int));
    int* y = alloca(sizeof(int));
    while (*x > 0 && *y > 0) {
        if (__VERIFIER_nondet_int()) {
            if (*x < *y) {
                *y = *x - 1;
            } else {
                *y = *y - 1;
            }
            *x = __VERIFIER_nondet_int();
        } else {
            if (*x < *y) {
                *x = *x - 1;
            } else {
                *x = *y - 1;
            }
            *y = __VERIFIER_nondet_int();
        }
    }
}