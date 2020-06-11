//#Safe
#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
    if (fma(4.0, 1.5, 4.0) != 24.0) {
	    __VERIFIER_error();
    }
    return 0;
}
