#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
    int i;
    float f;
    f = frexp(123.45, &i);
    if (i != 7) {
	    __VERIFIER_error();
    }
    if (f != 0.964453) {
	    __VERIFIER_error();
    }
    return 0;
}

