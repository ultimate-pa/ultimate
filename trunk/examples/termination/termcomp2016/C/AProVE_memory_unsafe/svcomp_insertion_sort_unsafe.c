extern int __VERIFIER_nondet_int(void);

void insertion(int a[], int N)
{
    int i, j, v;
    for (i = 2; i <= N; i++) {
        v = a[i];
        j = i;
        while (j > 0 && a[j - 1] > v) {
            a[j] = a[j-1];
            j--;
        }
        a[j] = v;
    }
}

int main() {
  int *a;
  int N = __VERIFIER_nondet_int();
  insertion(a, N);
  return 0;
}
