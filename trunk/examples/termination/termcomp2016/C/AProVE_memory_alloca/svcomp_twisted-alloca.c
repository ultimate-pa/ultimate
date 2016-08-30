#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int f(int k, int l)
{
    int* k_ref = alloca(sizeof(int));
    int* l_ref = alloca(sizeof(int));
    int* i = alloca(sizeof(int));
    int* j = alloca(sizeof(int));
    *k_ref = k;
    *l_ref = l;
    *i = 0;
    *j = 0;
L1: while (*i < *k_ref) {
        (*i)++;
        if (*i % 2) {
            continue;
        }
        goto L2;
    }
L2: while (*j < 1) {
        (*j)++;
        if (*i % 2) {
            continue;
        }
        goto L1;
    }
    return *i + *j;
}

int main() {
  return f(__VERIFIER_nondet_int(),__VERIFIER_nondet_int());
}