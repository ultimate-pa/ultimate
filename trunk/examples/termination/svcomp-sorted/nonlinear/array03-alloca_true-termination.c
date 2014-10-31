#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

void test_fun(int a[], int N)
{
    int i;
    int res;
    for (i = 0; i < N; i++) {
        res = 1;
        if (a[i] == 0) {
            res = 1;
        } else if (a[i] < 0) {
            res = 0;
        }
        while (a[i] > 0) {
            res = res * a[i];
            a[i]--;
        }
        a[i] = res;
    }
}

int main() {
  int array_size = __VERIFIER_nondet_int();
  if (array_size < 1) {
     array_size = 1;
  }
  int* numbers = (int*) alloca(array_size * sizeof(int));
  test_fun(numbers, array_size);
}
