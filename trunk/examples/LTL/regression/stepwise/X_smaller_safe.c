//#Safe
//@ ltl invariant positive: [](AP(y == 1) ==> X(AP(x == 2) ));
// Bug: Counterexample found although no counterexample should exists. End of program with X operator still 'evaluated' does report wrong counterexamples. 

#include <stdio.h> 
#include <assert.h>
#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_ltl_step() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int x,y;

int main()
{
	y = 1;
	__VERIFIER_ltl_step();
	x = 2;
	//y = 2;
	__VERIFIER_ltl_step();
	
}

