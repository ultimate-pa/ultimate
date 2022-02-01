//#Safe
//@ ltl invariant positive: [](AP(a == 1) ==> X(AP(a == 2)));

#include <stdio.h> 
#include <assert.h>
#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_ltl_step() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int a;
 
int getValue(int x){
	return x+1;
}

int main()
{
	a = 1;
	__VERIFIER_ltl_step();
	a = getValue(a);
	__VERIFIER_ltl_step();
}

