#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int* x;

int foo(void) {
    (*x)--;
}

int main() {
    x = alloca(sizeof(int));
    *x = __VERIFIER_nondet_int();
    
    while (*x > 0) {
        if (__VERIFIER_nondet_int()) {
            foo();
        } else {
            foo();
        }
    }
    return 0;
}