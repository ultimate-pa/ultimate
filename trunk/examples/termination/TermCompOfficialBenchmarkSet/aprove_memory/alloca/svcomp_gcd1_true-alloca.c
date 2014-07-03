#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int gcd(int x, int y) {
    int* x_ref = alloca(sizeof(int));
    int* y_ref = alloca(sizeof(int));
    int* r = alloca(sizeof(int));
    *x_ref = x;
    *y_ref = y;
    if (*x_ref < 0) *x_ref = -(*x_ref);
    if (*y_ref < 0) *y_ref = -(*y_ref);
    while (*y_ref > 0) {
        /* the next statements compute r = mod(x,y) */
        *r = *x_ref;
        while (*r >= *y_ref)
            *r = *r - *y_ref;
        /* end of inlined mod */
        *x_ref = *y_ref;
        *y_ref = *r;
    }
    return *x_ref;
}

int main() {
    int x,y;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    gcd(x,y);
}