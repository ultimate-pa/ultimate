//#Safe
/* Tests for conversions of integers.
 * The assert statements hold only on systems... TODO description.
 * 
 * Author: langt@informatik.uni-freiburg.de
 * Date: 18.08.2015
 */

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int main() {
  /* unsigned long long to signed int */
  if (sizeof(long long) > 4) {
    unsigned long long a = 4294967295ULL;
    signed int b = a;

    if (b != -1) {
      __VERIFIER_error();
    }
  }

  /* signed long long to signed int */
  if (sizeof(long long) > 4) {
    signed long long c = -9223372034707292161;
    signed int d = c;

    if (d != 2147483647) {
      __VERIFIER_error();
    }
  }

  /* unsigned int to signed int */
  if (sizeof(int) == 4) {
    unsigned int e = 4294967295U;
    signed int f = e;

    if (f != -1) {
      __VERIFIER_error();
    }
  }
}
