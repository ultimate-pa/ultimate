#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int main() {
    int* x = alloca(sizeof(int));
    int* y = alloca(sizeof(int));
    int* z = alloca(sizeof(int));
    *x = __VERIFIER_nondet_int();
    *y = __VERIFIER_nondet_int();
    *z = __VERIFIER_nondet_int();
    
    while (*x > 0) {
        *x = *x + *y;
        *y = *z;
        *z = -(*z) - 1;
    }
}