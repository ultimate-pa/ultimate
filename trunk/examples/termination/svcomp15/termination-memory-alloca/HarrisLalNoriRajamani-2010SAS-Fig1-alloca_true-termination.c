#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

void f(int d) {
    int* d_ref = alloca(sizeof(int));
    int* x = alloca(sizeof(int));
    int* y = alloca(sizeof(int));
    int* k = alloca(sizeof(int));
    int* z = alloca(sizeof(int));
    *d_ref = d;
    *x = 1;
    *y = 1;
    *k = 1;
    *z = 1;
    
    if (*k > 1073741823) {
        return;
    }
    L1:
    while (*z < *k) {
        *z = 2 * (*z);
    }
    L2:
    while (*x > 0 && *y > 0) {
        if (__VERIFIER_nondet_int()) {
            P1:
            *x = *x - *d_ref;
            *y = __VERIFIER_nondet_int();
            *z = *z - 1;
        } else {
            *y = *y - *d_ref;
        }
    }
}

int main() {
    if (__VERIFIER_nondet_int()) {
        f(1);
    } else {
        f(2);
    }
}