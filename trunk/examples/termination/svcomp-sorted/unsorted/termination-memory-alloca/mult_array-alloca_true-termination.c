#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);

int main() {
  int i, j;
  int length = __VERIFIER_nondet_int();
  if (length < 1) length = 1;
  int fac = __VERIFIER_nondet_int();
  if (fac < 1) fac = 1;
  int *arr = alloca(length*sizeof(int));
  int *arr2 = alloca(fac*length*sizeof(int));
  if (!arr || !arr2) return 0;
  for (i=0; i<length; i++) {
    arr[i] = __VERIFIER_nondet_int();
  }
  for (j=0; j<length*fac; j++) {
    arr2[j] = arr[i % length];
  }
  return 0;
}
