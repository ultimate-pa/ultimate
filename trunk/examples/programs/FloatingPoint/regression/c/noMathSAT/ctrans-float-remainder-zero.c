//#Safe
/*
	https://en.cppreference.com/w/c/numeric/math/remainder
*/

#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
  double r = remainder(0.0, 1);
	__VERIFIER_assert(r == 0 && !signbit(r));
  r = remainder(-0.0, 1);
	__VERIFIER_assert(r == 0 && signbit(r));

	return 0;
}

