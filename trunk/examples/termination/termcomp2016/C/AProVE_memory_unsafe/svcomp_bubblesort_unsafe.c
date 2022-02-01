extern int __VERIFIER_nondet_int(void);

void bubbleSort(int numbers[], int array_size)
{
    int i, j, temp;
     
    for (i = (array_size - 1); i >= 0; i--) {
        for (j = 1; j <= i; j++) {
            if (numbers[j-1] > numbers[j]) {
                temp = numbers[j-1];
                numbers[j-1] = numbers[j];
                numbers[j] = temp;
            }
        }
    }
}

int main() {
  int* numbers;
  int array_size = __VERIFIER_nondet_int();
  bubbleSort(numbers, array_size);
  return 0;
}
