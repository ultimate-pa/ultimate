#include <stdio.h> 
#include <assert.h>
#include <math.h>

//#Safe
//@ ltl invariant positive: [](AP(a==1) ==> X(AP(a==2)));

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_ltl_step() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int a, x = 5;

int main()
{
	x = 99;
	a = 1;
	__VERIFIER_ltl_step();
	if (x > 5){
		a = 2;
	} else {
		a = 6;
	}
	x = 0;
	__VERIFIER_ltl_step();
	a = 9;
}

