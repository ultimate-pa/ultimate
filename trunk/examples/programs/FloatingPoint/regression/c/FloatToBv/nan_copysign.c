#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
    if (copysign(1.0,-NaN) != -1.0) {
	    __VERIFIER_error();
    }
    if (signbit(copysign(-NaN,1.0)) != 0) {
	    __VERIFIER_error();
    }
    return 0;
}
