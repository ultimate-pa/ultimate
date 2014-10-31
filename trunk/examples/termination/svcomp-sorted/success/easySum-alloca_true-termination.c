#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int iterate(int bound)
{
    int* bound_ref = alloca(sizeof(int));
    int* i = alloca(sizeof(int));
    int* sum = alloca(sizeof(int));
    *bound_ref = bound;
    *sum = 0;
    for (*i = 0; *i < *bound_ref; (*i)++) {
        *sum += *i;
    }
    return *sum;
}

int main() {
  return iterate(__VERIFIER_nondet_int());
}
