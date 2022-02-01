#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int test_fun(int i, int j)
{
    int* i_ref = alloca(sizeof(int));
    int* j_ref = alloca(sizeof(int));
    int* c = alloca(sizeof(int));
    *i_ref = i;
    *j_ref = j;
    *c = 0;
    while (*i_ref >= 0) {
        *j_ref = 0;
        while (*j_ref <= *i_ref - 1) {
            *j_ref = *j_ref + 1;
            *c = *c + 1;
        }
        *i_ref = *i_ref - 1;
    }
    return *c;
}

int main() {
  return test_fun(__VERIFIER_nondet_int(),__VERIFIER_nondet_int());
}
