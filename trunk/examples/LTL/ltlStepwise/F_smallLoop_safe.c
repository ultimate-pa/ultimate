//#Unsafe
//@ ltl invariant positive: []((AP(open >= 0)) ==> (<> AP(open<= 0)));

#include <stdio.h> 
#include <assert.h>
#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_ltl_step();
extern int __VERIFIER_nondet_int();

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

