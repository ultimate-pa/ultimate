//#Safe
/*  
    https://en.cppreference.com/w/c/numeric/math/copysign
*/

#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
    __VERIFIER_assert(isnan(copysign(NAN,1.0)));
    __VERIFIER_assert(isnan(copysign(NAN,-1.0)));
    return 0;
}