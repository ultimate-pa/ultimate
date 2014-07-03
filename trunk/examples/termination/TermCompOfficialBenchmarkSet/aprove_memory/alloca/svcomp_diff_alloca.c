#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

void diff(int *A, int Alen, int *B, int Blen, int *D)
{
    int k = 0;
    int i = 0;
    int l1 = Alen;
    int l2 = Blen;
    int found;

    while (i < l1) {
        int j = 0;
        found = 0;
        while (j < l2 && !found) {
            if(A[i] == B[j]) {
                found = 1;
            } else {
                j++;
            }
        }
        if (!found) {
            D[k] = A[i];
            k++;
        }
        i++;
    }
}

int main() {
  int Alen = __VERIFIER_nondet_int();
  int Blen = __VERIFIER_nondet_int();
  if (Alen < 1) {
     Alen = 1;
  }
  if (Blen < 1) {
     Blen = 1;
  }
  int* A = (int*) alloca(Alen * sizeof(int));
  int* B = (int*) alloca(Blen * sizeof(int));
  int* D = (int*) alloca(Alen * sizeof(int));
  diff(A, Alen, B, Blen, D);
  return 0;
}
