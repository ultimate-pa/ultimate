extern unsigned int __VERIFIER_nondet_uint(void);
extern void __VERIFIER_error();

unsigned int sum(unsigned int n, unsigned int m) {
    if (n == 0) {
      return m;
    } else {
      return sum(n - 1, m + 1);
    }
}

int main(void) {
  unsigned int a = __VERIFIER_nondet_uint();
  unsigned int b = __VERIFIER_nondet_uint();
  unsigned int result = sum(a, b);
  if (result != a + b) {
    ERROR: __VERIFIER_error();
  }
}