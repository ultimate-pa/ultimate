#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int main() {
    int* x = alloca(sizeof(int));
    int* debug = alloca(sizeof(int));
    *x = __VERIFIER_nondet_int();
    *debug = 0;
    
    while (*x < 255) {
        if (*x % 2 != 0) {
            (*x)--;
        } else {
            *x += 2;
        }
        if (*debug != 0) {
            *x = 0;
        }
    }
    return 0;
}