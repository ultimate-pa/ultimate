#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int f(int a) {
    int* a_ref = alloca(sizeof(int));
    int* tmp = alloca(sizeof(int));
    int* count = alloca(sizeof(int));
    *a_ref = a;
    *tmp = 0;
    *count = 0;
    while (*a_ref > 1) {
        *tmp = *a_ref % 2;
        if (*tmp == 0) *a_ref = *a_ref / 2;
        else *a_ref = *a_ref - 1;
        (*count)++;
    }
    return *count;
}

int main() {
    int x = __VERIFIER_nondet_int();
    int count = f(x);
    return count;
}