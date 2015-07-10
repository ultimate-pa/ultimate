extern int __VERIFIER_nondet_int(void);

void SelectionSort(int a[], int array_size)
{
    int i;
    for (i = 0; i < array_size - 1; ++i)
    {
        int j, min, temp;
        min = i;
        for (j = i+1; j < array_size; ++j)
        {
            if (a[j] < a[min])
                min = j;
        }
        
        temp = a[i];
        a[i] = a[min];
        a[min] = temp;
    }
}

int main() {
  int *a;
  int array_size = __VERIFIER_nondet_int();
  SelectionSort(a, array_size);
  return 0;
}  
