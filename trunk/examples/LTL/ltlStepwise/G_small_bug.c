#include <stdio.h> 
#include <assert.h>
#include <math.h>

//#Safe
//@ ltl invariant positive: []( AP(a >= b) ) ;

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_ltl_step() __attribute__ ((__noreturn__));

int a = 5;
int b = 3;
	
	
int main()
{
	__VERIFIER_ltl_step();
	b = 2 * b;
	a = a - b; 
	__VERIFIER_ltl_step();
}

