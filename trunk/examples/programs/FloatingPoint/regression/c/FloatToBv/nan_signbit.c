//#Safe
#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
    if (signbit(-NaN) == 0.0) {
	    __VERIFIER_error();
    }
    if (signbit(NaN) != 0.0) {
	    __VERIFIER_error();
    }
    return 0;
}
