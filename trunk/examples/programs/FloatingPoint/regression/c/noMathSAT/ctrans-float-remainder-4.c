//#Safe
/*
	https://en.cppreference.com/w/c/numeric/math/remainder
*/

#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
	__VERIFIER_assert(remainderf(-5.1f, 3) == 0x1.ccccdp-1);

	return 0;
}

