extern int __VERIFIER_nondet_int(void);

void sort(int *x, int n) {
    int pass;
    int i;
    for (pass=1; pass < n; pass++)  // count how many times
        // This next loop becomes shorter and shorter
        for (i=0; i < n - pass; i++)
            if (x[i] > x[i+1]) {
                // exchange elements
                int temp = x[i]; x[i] = x[i+1];  x[i+1] = temp;
            }
}

int main() {
  int *x;
  int n = __VERIFIER_nondet_int();
  sort(x, n);
  return 0;
}
