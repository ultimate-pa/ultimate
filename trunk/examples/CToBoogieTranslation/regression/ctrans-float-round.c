/*  
    https://en.cppreference.com/w/c/numeric/math/round
*/

#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
	//round
	__VERIFIER_assert(round(2.7) == 3.0);
	__VERIFIER_assert(round(2.5) == 3.0);
	__VERIFIER_assert(round(2.3) == 2.0);
	
	__VERIFIER_assert(round(-2.7) == -3.0);
	__VERIFIER_assert(round(-2.5) == -3.0);
	__VERIFIER_assert(round(-2.3) == -2.0);
	
	__VERIFIER_assert(round(-0) == -0.0);
	__VERIFIER_assert(round(+0) == +0.0);
	__VERIFIER_assert(round(-INFINITY) == -INFINITY);
	__VERIFIER_assert(round(INFINITY) == INFINITY);
	
	int i = isnan(round(NAN));
    __VERIFIER_assert(i);
	
	// lround
	__VERIFIER_assert(lround(2.7) == (long)3.0);
	__VERIFIER_assert(lround(2.5) == (long)3.0);
	__VERIFIER_assert(round(2.3) == (long)2.0);
	
	__VERIFIER_assert(lround(-2.7) == (long)-3.0);
	__VERIFIER_assert(lround(-2.5) == (long)-3.0);
	__VERIFIER_assert(lround(-2.3) == (long)-2.0);
	
	__VERIFIER_assert(lround(-0) == (long)-0.0);
	__VERIFIER_assert(lround(+0) == (long)+0.0);
	
	// llround
	__VERIFIER_assert(llround(2.7) == (long long)3.0);
	__VERIFIER_assert(llround(2.5) == (long long)3.0);
	__VERIFIER_assert(llround(2.3) == (long long)2.0);
	
	__VERIFIER_assert(llround(-2.7) == (long long)-3.0);
	__VERIFIER_assert(llround(-2.5) == (long long)-3.0);
	__VERIFIER_assert(llround(-2.3) == (long long)-2.0);
	
	__VERIFIER_assert(llround(-0) == (long long)-0.0);
	__VERIFIER_assert(llround(+0) == (long long)+0.0);
	
    return 0;
}