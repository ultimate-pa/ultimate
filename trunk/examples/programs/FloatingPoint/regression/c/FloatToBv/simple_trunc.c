#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
    if (trunc(1.9) != 1.000000) {
	    __VERIFIER_error();
    }
    if (trunc(-2.7) != 2.000000) {
	    __VERIFIER_error();
    }
    return 0;
}

