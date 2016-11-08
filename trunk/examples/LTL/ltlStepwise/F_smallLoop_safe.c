#include <stdio.h> 
#include <assert.h>
#include <math.h>

//#Unsafe
//@ ltl invariant positive: []((AP(open >= 0)) ==> (<> AP(open<= 0)));

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_ltl_step() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int open = 0; 

int main()
{
	while(1){
		open =__VERIFIER_nondet_int();
		__VERIFIER_ltl_step();
		while(open > 0){
			open--;
		}
		__VERIFIER_ltl_step();
	}
}

