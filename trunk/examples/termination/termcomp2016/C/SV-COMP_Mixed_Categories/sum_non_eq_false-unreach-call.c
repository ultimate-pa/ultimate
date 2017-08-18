//#termcomp16-someonesaidno
extern void __VERIFIER_error();

int sum(int n, int m) {
    if (n == 0) {
      return m;
    } else {
      return sum(n - 1, m + 1);
    }
}

int main(void) {
  int a;
  int b;
  int result = sum(a, b);
  if (result == a + b) {
    ERROR: __VERIFIER_error();
  }
}
