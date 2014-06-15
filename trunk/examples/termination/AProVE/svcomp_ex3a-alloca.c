#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int test_fun(int x)
{
    int* x_ref = alloca(sizeof(int));
    int* c = alloca(sizeof(int));
    *x_ref = x;
    *c = 0;
    while ((*x_ref > 1) && (*x_ref < 100)) {
        *x_ref = (*x_ref) * (*x_ref);
        *c = *c + 1;
    }
    return *c;
}

int main() {
  return test_fun(__VERIFIER_nondet_int());
}
