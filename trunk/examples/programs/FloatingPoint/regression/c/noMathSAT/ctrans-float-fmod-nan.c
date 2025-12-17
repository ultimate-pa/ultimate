//#Safe
/*  
    https://en.cppreference.com/w/c/numeric/math/fmod
*/

#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
  int i = isnan(fmod(5.1,0));
  __VERIFIER_assert(i);
	i = isnan(fmod(5.1,-0));
    __VERIFIER_assert(i);
	
	i = isnan(fmod(NAN,3));
	__VERIFIER_assert(i);
	i = isnan(fmod(5.1,NAN));
	__VERIFIER_assert(i);
    
  return 0;
}
