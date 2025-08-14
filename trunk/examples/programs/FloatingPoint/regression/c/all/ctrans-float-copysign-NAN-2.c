//#Safe
/*  
    https://en.cppreference.com/w/c/numeric/math/copysign
*/

#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{

    
    double x = NAN;
    double y = -NAN;
    double csy = copysign(NAN,-1.0);
    
    //long long bv_y;
    //long long bv_csy;
    
    //__VERIFIER_assert(sizeof(long long) == sizeof(double));
    
    __VERIFIER_assert(isnan(x));
    __VERIFIER_assert(isnan(y));
    __VERIFIER_assert(isnan(csy));
    __VERIFIER_assert(x != x);

    //memcpy(&bv_y, &y, sizeof y);
    //memcpy(&bv_csy, &csy, sizeof csy);
    //__VERIFIER_assert(bv_y == bv_csy);
    return 0;
}