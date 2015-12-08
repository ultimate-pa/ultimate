#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int test_fun(int x, int y)
{
    int* x_ref = alloca(sizeof(int));
    int* y_ref = alloca(sizeof(int));
    *x_ref = x;
    *y_ref = y;
    while ((*x_ref > 0) && (*y_ref > 0)) {
        if (*x_ref > *y_ref) {
            while (*x_ref > 0) {
                *x_ref = *x_ref - 1;
            }
        } else {
            while (*y_ref > 0) {
                *y_ref = *y_ref - 1;
            }
        }
    }
    return *x_ref + *y_ref;
}

int main() {
  return test_fun(__VERIFIER_nondet_int(),__VERIFIER_nondet_int());
}
