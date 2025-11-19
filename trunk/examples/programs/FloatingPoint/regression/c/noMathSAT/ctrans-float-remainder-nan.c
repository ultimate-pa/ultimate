//#Safe
/*
	https://en.cppreference.com/w/c/numeric/math/remainder
*/

#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
	int i = isnan(remainder(5.1, 0));
	__VERIFIER_assert(i);
	i = isnan(remainder(5.1, -0));
	__VERIFIER_assert(i);
	
	i = isnan(remainder(NAN, 3));
	__VERIFIER_assert(i);
	i = isnan(remainder(5.1, NAN));
	__VERIFIER_assert(i);

	return 0;
}

