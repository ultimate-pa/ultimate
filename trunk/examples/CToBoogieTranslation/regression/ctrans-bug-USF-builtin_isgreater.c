//#Safe
/*

DD 2017-11-16


   ; comparison operators
   ; Note that all comparisons evaluate to false if either argument is NaN
   (fp.leq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
   (fp.lt  (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable) 
   (fp.geq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable) 
   
   (fp.gt  (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)

*/

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } return; }

int main(void)
{
    __VERIFIER_assert(__builtin_isgreaterequal(2.0, 1.0));
    __VERIFIER_assert(!__builtin_isgreaterequal(1.0, 2.0));
    __VERIFIER_assert(__builtin_isgreaterequal(1.0, 1.0));
    __VERIFIER_assert(__builtin_isgreaterequal((__builtin_inff()), 1.0));
    __VERIFIER_assert(!__builtin_isgreaterequal(1.0, (__builtin_nanf (""))));

    return 0;
}

