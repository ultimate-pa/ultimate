extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();
void reach_error() { __assert_fail("0", "many-labels.c", 3, "reach_error"); }

int main() {
  int x = __VERIFIER_nondet_int();
  if (x < 0) {
    return;
  }

  if (x == -8) {
    goto LABEL_A;
  }
  if (x == -16) {
    goto LABEL_B;
  }
  if (x == -32) {
    goto LABEL_C;
  }
  if (x == -64) {
    goto LABEL_D;
  }
  return (0);

  LABEL_A:
  LABEL_B:
  LABEL_C:
  LABEL_D: {reach_error();abort();}
  return (-1);
}

