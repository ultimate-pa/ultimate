#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int main() {
    int* x = alloca(sizeof(int));
    int* y = alloca(sizeof(int));
    while (*x != 0 && *y > 0) {
        if (*x > 0) {
            if (__VERIFIER_nondet_int()) {
                *x = *x - 1;
                *y = __VERIFIER_nondet_int();
            } else {
                *y = *y - 1;
            }
        } else {
            if (__VERIFIER_nondet_int()) {
                *x = *x + 1;
            } else {
                *y = *y - 1;
                *x = __VERIFIER_nondet_int();
            }
        }
    }
}