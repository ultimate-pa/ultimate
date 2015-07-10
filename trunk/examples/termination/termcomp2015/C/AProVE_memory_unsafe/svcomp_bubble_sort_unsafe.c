extern int __VERIFIER_nondet_int(void);

void bubble(int a[], int N)
{
    int i, j, t;
    for (i = N; i >= 1; i--) {
        for (j = 2; j <= i; j++) {
            if (a[j-1] > a[j]) {
                t = a[j-1];
                a[j-1] = a[j];
                a[j] = t;
            }
        }
    }
}

int main() {
  int* a;
  int n = __VERIFIER_nondet_int();
  bubble(a, n);
  return 0;
}
