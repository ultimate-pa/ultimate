//#Safe
#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
    float f;
    float g;
    f = modf(123.45, &g);
    if (f != 123.0) {
	    __VERIFIER_error();
    }
    if (g != 0.45) {
	    __VERIFIER_error();
    }
    return 0;
}

