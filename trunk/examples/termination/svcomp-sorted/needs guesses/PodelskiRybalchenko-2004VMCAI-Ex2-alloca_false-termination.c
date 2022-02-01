#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int main() {
    int* x = alloca(sizeof(int));
    *x = __VERIFIER_nondet_int();
    while (*x >= 0) {
        *x = 2 * (*x) + 10;
    }
    return 0;
}