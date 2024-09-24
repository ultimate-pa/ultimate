//#Safe
/*  
    https://en.cppreference.com/w/c/numeric/math/trunc
*/

#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
	 __VERIFIER_assert(trunc(2.7) == 2.0);
	 __VERIFIER_assert(trunc(-2.7) == -2.0);
	 __VERIFIER_assert(trunc(-0) == -0.0);
	 __VERIFIER_assert(trunc(+0) == +0.0);
	 __VERIFIER_assert(trunc(-INFINITY) == -INFINITY);
	 __VERIFIER_assert(trunc(INFINITY) == INFINITY);
	 int i = isnan(trunc(NAN));
    __VERIFIER_assert(i);
    
    return 0;
}