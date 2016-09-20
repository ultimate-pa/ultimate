#include <stdio.h> 
#include <assert.h>
#include <math.h>

//#Safe
//@ ltl invariant positive: []( AP(a > b) );

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_ltl_step() __attribute__ ((__noreturn__));

int a = 5;
int b = 3;
int tempa, tempb; 
	
	
void foo(int x, int y){
	b = x;
	a = y;
	tempa = a;
	a = -22;
	tempb = b;
	b = 2000;
	return;
}
	
int main()
{
	while(1){
		__VERIFIER_ltl_step();
		a = 20;
		__VERIFIER_ltl_step();
		foo(10, 20);
		foo(20, 10);
		__VERIFIER_ltl_step();
		foo(10, 20);
		a = tempa;
		b = tempb;
		__VERIFIER_ltl_step();
	}
}

