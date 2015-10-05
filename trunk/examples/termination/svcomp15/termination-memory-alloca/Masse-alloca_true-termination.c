#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int main() {
    int* x = alloca(sizeof(int));
    while (*x <= 1000) {
        if (__VERIFIER_nondet_int()) {
            *x = - 2 * (*x) + 2;
        } else {
            *x = - 3 * (*x) - 2;
        }
    }
}