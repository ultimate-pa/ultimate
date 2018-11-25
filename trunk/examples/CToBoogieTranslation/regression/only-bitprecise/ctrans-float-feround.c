/*  
    http://en.cppreference.com/w/c/numeric/fenv/feround
*/

#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
	
	
	__VERIFIER_assert(fesetround(0)==1); 
	__VERIFIER_assert(fegetround()==0); 
	
	__VERIFIER_assert(fesetround(1)==1); 
	__VERIFIER_assert(fegetround()==1);
	
	__VERIFIER_assert(fesetround(2)==1); 
	__VERIFIER_assert(fegetround()==2); 
	
	__VERIFIER_assert(fesetround(3)==1); 
	__VERIFIER_assert(fegetround()==3); 
	
	__VERIFIER_assert(fesetround(4)==0); 
	__VERIFIER_assert(fegetround()==3); 
    
    return 0;
}