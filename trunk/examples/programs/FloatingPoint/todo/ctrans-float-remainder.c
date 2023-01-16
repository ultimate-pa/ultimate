//#Safe
/*
	https://en.cppreference.com/w/c/numeric/math/remainder
*/

#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
    __VERIFIER_assert(remainder(5.1, 3) == -0.9);
	__VERIFIER_assert(remainder(-5.1, 3) == 0.9);
	__VERIFIER_assert(remainder(5.1, -3) == -0.9);
	__VERIFIER_assert(remainder(-5.1, -3) == 0.9);
	__VERIFIER_assert(remainder(0, 1) == 0.0);
	__VERIFIER_assert(remainder(-0, 1) == -0.0);
	
    __VERIFIER_assert(remainder(5.1,INFINITY) == 5.1);
	
	int i = isnan(remainder(INFINITY, 3));
	__VERIFIER_assert(i);
	i = isnan(remainder(-INFINITY, 3));
	__VERIFIER_assert(i);
	
    i = isnan(remainder(5.1,0));
    __VERIFIER_assert(i);
	i = isnan(remainder(5.1,-0));
    __VERIFIER_assert(i);
	
	i = isnan(remainder(NAN,3));
	__VERIFIER_assert(i);
	i = isnan(remainder(5.1,NAN));
	__VERIFIER_assert(i);

    return 0;
}

