//#Safe
/*  
    
    https://en.cppreference.com/w/c/numeric/math/signbit
    https://www.gnu.org/software/libc/manual/html_node/FP-Bit-Twiddling.html
    http://man7.org/linux/man-pages/man3/signbit.3.html
    
    Signbit
    
    Determines if the given floating point number arg is negative. The macro returns an integral value.

    This macro detects the sign bit of zeroes, infinities, and NaNs. Along with copysign, this macro is one of the only two portable ways to examine the sign of a NaN.
    
    Parameters      arg	- floating point value
    Return value    Nonzero integral value if arg is negative, ​0​ otherwise.
    
    
*/

#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
    int rtr;
    double x;
    x = +0.0;
    rtr = signbit(x);
    __VERIFIER_assert(rtr == 0);
    x = -0.0;
    rtr = signbit(x);
    __VERIFIER_assert(rtr != 0);
    x = NAN;
    rtr = signbit(x);
    __VERIFIER_assert(rtr == 0);
    x = 0.0 / 0.0;
    rtr = signbit(x);
    __VERIFIER_assert(rtr != 0);
    return 0;
}