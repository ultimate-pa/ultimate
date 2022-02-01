extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
extern unsigned int __VERIFIER_nondet_uint(void);

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}

int main(void) {
  unsigned int x = 1;
  unsigned int y = __VERIFIER_nondet_uint();

  __VERIFIER_assume(y > 0);

  while (x < y) {
    if (x < y / x) {
      x *= x;
    } else {
      x++;
    }
  }

  __VERIFIER_assert(x != y);
}
