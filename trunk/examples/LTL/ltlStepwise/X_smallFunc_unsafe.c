//#Safe
//@ ltl invariant positive: [](AP(a > b) ==> X(AP(b > c)));

#include <stdio.h> 
#include <assert.h>
#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_ltl_step() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int a, b, c;
 
int calc(int x, int y, int z){
	if (x > y){
		return z+1;
	}
	return y;
}

int main()
{
	a = __VERIFIER_nondet_int();
	b = __VERIFIER_nondet_int();
	c = __VERIFIER_nondet_int();
	
	__VERIFIER_ltl_step();
	c = calc(a,b,c);
	__VERIFIER_ltl_step();
}

