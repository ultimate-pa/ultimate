//#Safe
//@ ltl invariant positive: []( AP(a >= b) ) ;

#include <stdio.h> 
#include <assert.h>
#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_ltl_step() __attribute__ ((__noreturn__));

int a = 5;
int b = 3;
int c = 1;
	
	
int main()
{
	__VERIFIER_ltl_step();
	b = 6;
	a = a + b;
	c = 1;
	c = 1;
	__VERIFIER_ltl_step();
	c = 1;
	c = 1;
	__VERIFIER_ltl_step();
}

