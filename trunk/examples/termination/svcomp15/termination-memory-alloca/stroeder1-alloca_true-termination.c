#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int sumOfThirdBytes(int numbers[], int array_size)
{
    int i, sum;
    char* p;
    sum = 0;
    for (i = 0; i < array_size; i++) {
        p = &(numbers[i]);
        p = p + 2;
        sum = sum + *p;
    }
    return sum;
}

int main() {
  int array_size = __VERIFIER_nondet_int();
  if (array_size < 1) {
     array_size = 1;
  }
  int* numbers = (int*) alloca(array_size * sizeof(int));
  return sumOfThirdBytes(numbers, array_size);
}
