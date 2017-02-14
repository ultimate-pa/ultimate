//#Safe
//@ ltl invariant positive: [](AP(a == 1));
//Bug #81: reaching end of program without entering the main function (therefore always finding counterexample).

#include <stdio.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int a = 1;

int main()
{
	a = 1;
	__VERIFIER_assume(0);
}