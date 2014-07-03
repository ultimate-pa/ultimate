#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int main() {
    int* id = alloca(sizeof(int));
    int* maxId = alloca(sizeof(int));
    *id = __VERIFIER_nondet_int();
    *maxId = __VERIFIER_nondet_int();
    
    if (0 <= *id && *id < *maxId) {
        int* tmp = alloca(sizeof(int));
        *tmp = *id + 1;
        while (*tmp != *id && __VERIFIER_nondet_int()) {
            if (*tmp <= *maxId) {
                *tmp = *tmp + 1;
            } else {
                *tmp = 0;
            }
        }
    }
    return 0;
}