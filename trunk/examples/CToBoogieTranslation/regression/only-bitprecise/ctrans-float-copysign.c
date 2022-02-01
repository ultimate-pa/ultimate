/*  
    https://en.cppreference.com/w/c/numeric/math/copysign
*/

#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
	 __VERIFIER_assert(copysign(1,2) == 1.0);
	 __VERIFIER_assert(copysign(1,-2) == -1.0);
	 __VERIFIER_assert(copysign(-INFINITY,1) == INFINITY);
	 __VERIFIER_assert(copysign(INFINITY,-1) == -INFINITY);
	 int i = isnan(copysign(NAN,1));
    __VERIFIER_assert(i);
    
    return 0;
}