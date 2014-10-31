#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int main() {
    int* x = alloca(sizeof(int));
    int* y = alloca(sizeof(int));
    int* z = alloca(sizeof(int));
    
    while (*x > 0 && *y > 0 && *z > 0) {
        if (__VERIFIER_nondet_int()) {
            *x = *x - 1;
        } else if (__VERIFIER_nondet_int()) {
            *y = *y - 1;
            *z = __VERIFIER_nondet_int();
        } else {
            *z = *z - 1;
            *x = __VERIFIER_nondet_int();
        }
    }
}