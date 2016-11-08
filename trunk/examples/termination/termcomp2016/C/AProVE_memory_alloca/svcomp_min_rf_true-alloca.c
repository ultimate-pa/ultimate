#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int main() {
    int* x = alloca(sizeof(int));
    int* y = alloca(sizeof(int));
    int* z = alloca(sizeof(int));
    *x = __VERIFIER_nondet_int();
    *y = __VERIFIER_nondet_int();
    
    while (*y > 0 && *x > 0) {
        if (*x > *y) *z = *y;
        else *z = *x;
        if (__VERIFIER_nondet_int()) {*y = *y + *x; *x = *z - 1; *z = *y + *z; }
        else {*x = *y + *x; *y = *z - 1; *z = *x + *z; }
    }
}