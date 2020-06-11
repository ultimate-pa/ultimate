#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
    if (fdim(10.0, 5.0) != 5.0) {
	    __VERIFIER_error();
    }
    if (fdim(5.0, 10.0) != 0.0) {
	    __VERIFIER_error();
    }
    return 0;
}
