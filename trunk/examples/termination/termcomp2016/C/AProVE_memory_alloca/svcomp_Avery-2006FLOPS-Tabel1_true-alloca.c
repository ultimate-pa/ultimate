#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int subxy(int x, int y) {
    int* x_ref = alloca(sizeof(int));
    int* y_ref = alloca(sizeof(int));
    int* z = alloca(sizeof(int));
    int* i = alloca(sizeof(int));
    *x_ref = x;
    *y_ref = y;
    *z = 0;
    *i = *x_ref;
    if (*y_ref <= 0 || *x_ref <= 0) {
        return 0;
    }
    while (*i > 0) {
        (*i)--;
        (*z)++;
    }
    while (*i < *y_ref) {
        (*i)++;
        (*z)--;
    }
    return *z;
}

int main() {
    int x = __VERIFIER_nondet_int();
    int y = __VERIFIER_nondet_int();
    subxy(x,y);
    return 0;
}