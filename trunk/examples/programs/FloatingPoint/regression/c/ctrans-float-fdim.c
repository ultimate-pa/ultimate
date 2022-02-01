//#Safe
/*  
    https://en.cppreference.com/w/c/numeric/math/fdim
*/

#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
	__VERIFIER_assert(fdim(4,1) == 3.0);
	__VERIFIER_assert(fdim(1,4) == 0.0);
	__VERIFIER_assert(fdim(4,-1) == 5.0);
	__VERIFIER_assert(fdim(1,-4) == 5.0);
	 
	int i = isnan(fdim(NAN,1));
    __VERIFIER_assert(i);
	i = isnan(fdim(1,NAN));
    __VERIFIER_assert(i);
    
    return 0;
}