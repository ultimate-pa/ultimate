#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int gcd(int y1, int y2) {
    int* y1_ref = alloca(sizeof(int));
    int* y2_ref = alloca(sizeof(int));
    *y1_ref = y1;
    *y2_ref = y2;
    
    while (*y1_ref != *y2_ref) {
        if (*y1_ref > *y2_ref) {
            *y1_ref = *y1_ref - *y2_ref;
        } else {
            *y2_ref = *y2_ref - *y1_ref;
        }
    }
    return *y1_ref;
}

int main() {
    int y1 = __VERIFIER_nondet_int();
    int y2 = __VERIFIER_nondet_int();
    if (y1 >= 0 && y2 >= 0) {
        gcd(y1, y2);
    }
    return 0;
}