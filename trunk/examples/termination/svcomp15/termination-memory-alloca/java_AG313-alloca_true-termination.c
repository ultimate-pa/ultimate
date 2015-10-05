#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int quot(int x, int y)
{
    int* x_ref = alloca(sizeof(int));
    int* y_ref = alloca(sizeof(int));
    int* i = alloca(sizeof(int));
    *x_ref = x;
    *y_ref = y;
    *i = 0;
    if (*x_ref == 0) return 0;
    while ((*x_ref > 0) && (*y_ref > 0)) {
        *i += 1;
        *x_ref = (*x_ref - 1) - (*y_ref - 1);
    }
    return *i;
}

int main() {
  return quot(__VERIFIER_nondet_int(),__VERIFIER_nondet_int());
}
