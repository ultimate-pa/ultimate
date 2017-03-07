//#Safe
//@ ltl invariant positive: [](AP(a==1) ==> X(AP(b==2)));

#include <stdio.h> 
#include <assert.h>
#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_ltl_step() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int a,x,b;

int main()
{
	x = 99;
	a = 1;
	__VERIFIER_ltl_step();
	b = 2;
	__VERIFIER_ltl_step();
	x = 6;
	__VERIFIER_ltl_step();
	x = 0;
	__VERIFIER_ltl_step();
	x = 9;
}

