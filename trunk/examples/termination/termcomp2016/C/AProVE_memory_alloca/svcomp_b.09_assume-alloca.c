#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int test_fun(int x, int y)
{
    int* x_ref = alloca(sizeof(int));
    int* y_ref = alloca(sizeof(int));
    int* c = alloca(sizeof(int));
    *x_ref = x;
    *y_ref = y;
    *c = 0;
    if (*x_ref <= 0 || *y_ref <= 0) {
        // replace assume
        return *x_ref + *y_ref;
    }
    while (!(*x_ref == 0)) {
        if (*x_ref > *y_ref) {
            *x_ref = *y_ref;
        } else {
            if (*x_ref <= 0) {
                // replace assume
                return *x_ref;
            }
            *x_ref = *x_ref - 1;
        }
        *c = *c + 1;
    }
    return *c;
}

int main() {
  return test_fun(__VERIFIER_nondet_int(),__VERIFIER_nondet_int());
}
