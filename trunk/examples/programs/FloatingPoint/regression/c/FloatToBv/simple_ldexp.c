#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
    if (ldexp(7.0, -4) != 0.437500) {
	    __VERIFIER_error();
    }
    return 0;
}

