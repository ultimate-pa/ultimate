//#Safe
/*  
    https://en.cppreference.com/w/c/numeric/math/floor
*/

#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
	 __VERIFIER_assert(floor(2.7) == 2.0);
	 __VERIFIER_assert(floor(-2.7) == -3.0);
	 __VERIFIER_assert(floor(-0) == -0.0);
	 __VERIFIER_assert(floor(+0) == +0.0);
	 __VERIFIER_assert(floor(-INFINITY) == -INFINITY);
	 __VERIFIER_assert(floor(INFINITY) == INFINITY);
	 int i = isnan(floor(NAN));
    __VERIFIER_assert(i);
    
    return 0;
}