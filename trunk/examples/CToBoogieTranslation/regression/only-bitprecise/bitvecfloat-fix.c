//#Safe
/*  
    https://en.cppreference.com/w/c/numeric/math/copysign
*/

#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
	float f = 1.0f + 1.0f;
	return 0;
}
