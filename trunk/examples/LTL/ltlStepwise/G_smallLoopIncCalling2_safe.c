//#Safe
//@ ltl invariant positive: []( AP(a > b) );

#include <stdio.h> 
#include <assert.h>
#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_ltl_step() __attribute__ ((__noreturn__));

int a = 5;
int b = 3;
int tempa = 33, tempb = 13; 
	
	
void foo(int x, int y){
	b = x;
	a = y;
	return;
}
	
int main()
{
	while(1){
		a = 20;
		foo(33, 1);
		a = 100;
		foo(200, -44);
		foo(33, 1);
		a = 100;
		a = tempa;
		b = tempb;
		__VERIFIER_ltl_step();
	}
}

