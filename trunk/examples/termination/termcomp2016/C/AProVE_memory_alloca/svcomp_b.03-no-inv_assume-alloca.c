#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int test_fun(int x, int y)
{
    int* x_ref = alloca(sizeof(int));
    int* y_ref = alloca(sizeof(int));
    *x_ref = x;
    *y_ref = y;
    if (*x_ref <= 0) {
        // replace assume
        return *y_ref;
    }
    while (*x_ref > *y_ref) {
        *y_ref = *y_ref + *x_ref;
    }
    return *y_ref;
}

int main() {
  return test_fun(__VERIFIER_nondet_int(),__VERIFIER_nondet_int());
}
