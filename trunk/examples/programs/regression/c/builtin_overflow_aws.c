//#Safe
/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2024-11-11
 *
 * Extracted from aws-c-common/aws_add_size_checked_harness.i
 */

int main() {
  unsigned long long a = __VERIFIER_nondet_ulonglong();
  unsigned long long b = __VERIFIER_nondet_ulonglong();
  unsigned long long r;
  if (!__builtin_uaddll_overflow(a, b, &r)) {
    //@ assert r == a + b;
  } else {
    //@ assert b > 0 && a > 18446744073709551615UL - b;
  }
}
