//#Safe
/*
    DD 2017-11-16

    We map fmin and fmax to SMTLIB FP functions 
   (fp.min (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)) 
   (fp.max (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
    
    http://en.cppreference.com/w/c/numeric/math/fmin
    http://en.cppreference.com/w/c/numeric/math/fmax
    
    Notes from SMTLIB: 
    ; comparison operators
    ; Note that all comparisons evaluate to false if either argument is NaN
    (fp.leq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
    (fp.lt  (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable) 
    (fp.geq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable) 
    (fp.gt  (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)

*/

#include <math.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
    float f = copysign(NaN, -1.0);
    float g = copysign(1.0, f);
    __VERIFIER_assert(g == -1.0);

    return 0;
}

