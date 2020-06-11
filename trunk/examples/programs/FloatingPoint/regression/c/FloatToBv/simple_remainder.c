//#Safe
#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
    if (remainder(6.3, 3.0) != 0.3) {
	    __VERIFIER_error();
    }
    return 0;
}

