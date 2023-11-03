//#Safe
#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
  double x; 
  x = copysign(1.0, +2.0);
  __VERIFIER_assert(x == 1.0);
  x = copysign(1.0, -2.0);
  __VERIFIER_assert(x == -1.0);
  x = copysign(-1.0, +2.0);
  __VERIFIER_assert(x == 1.0);
  x = copysign(-1.0, -2.0);
  __VERIFIER_assert(x == -1.0);
  x = copysign(INFINITY, -2.0);
  __VERIFIER_assert(x == -INFINITY);

  x = copysign(NAN, -2.0);
  __VERIFIER_assert(isnan(x));
  __VERIFIER_assert(signbit(x));
}