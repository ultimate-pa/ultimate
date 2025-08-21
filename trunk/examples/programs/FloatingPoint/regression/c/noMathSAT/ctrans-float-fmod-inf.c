//#Safe
/*  
    https://en.cppreference.com/w/c/numeric/math/fmod
*/

#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
	__VERIFIER_assert(fmod(5.1, INFINITY) == 5.1);
	__VERIFIER_assert(fmod(5.1, -INFINITY) == 5.1);
  
  int i = isnan(fmod(INFINITY, 3));
	__VERIFIER_assert(i);
	i = isnan(fmod(-INFINITY, 3));
	__VERIFIER_assert(i);

	return 0;
}