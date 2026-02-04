//#Safe
/*  
    https://en.cppreference.com/w/c/numeric/math/fmod
*/

#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
	__VERIFIER_assert(fmodf(5.1f, 3) == 2.1f);

	return 0;
}
