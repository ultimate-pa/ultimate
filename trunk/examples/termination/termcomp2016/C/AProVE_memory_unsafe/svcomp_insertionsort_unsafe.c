extern int __VERIFIER_nondet_int(void);

void insertionSort(int a[], int array_size)
{
    int i, j, index;
    for (i = 1; i < array_size; ++i)
    {
        index = a[i];
        for (j = i; j > 0 && a[j-1] > index; j--)
            a[j] = a[j-1];

        a[j] = index;
    }
}

int main() {
  int *a;
  int array_size = __VERIFIER_nondet_int();
  insertionSort(a, array_size);
  return 0;
}
