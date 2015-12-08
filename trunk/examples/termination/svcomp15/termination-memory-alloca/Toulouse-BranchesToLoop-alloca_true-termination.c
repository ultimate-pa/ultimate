#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int main() {
    int* x = alloca(sizeof(int));
    int* y = alloca(sizeof(int));
    int* z = alloca(sizeof(int));
    int* m = alloca(sizeof(int));
    int* n = alloca(sizeof(int));
    if (__VERIFIER_nondet_int()) {
        *x = 1;
    } else {
        *x = -1;
    }
    while (*y < 100 && *z < 100) {
        *y = *y + *x;
        *z = *z - *x;
    }
    return 0;
}