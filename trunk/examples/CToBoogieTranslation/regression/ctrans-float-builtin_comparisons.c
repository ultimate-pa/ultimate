//#Safe
/*
    DD 2017-11-16

    Various FP comparison via built-in functions. 
    
    We map them to SMTLIB FP functions and should get the desired behavior. 
    
    http://en.cppreference.com/w/c/numeric/math/isless
    http://en.cppreference.com/w/c/numeric/math/islessequal
    http://en.cppreference.com/w/c/numeric/math/isgreater
    http://en.cppreference.com/w/c/numeric/math/isgreaterequal
    http://en.cppreference.com/w/c/numeric/math/isunordered
    http://en.cppreference.com/w/c/numeric/math/islessgreater
    
    
    Notes from SMTLIB: 
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
    __VERIFIER_assert(__builtin_isgreaterequal((__builtin_inff ("")), 1.0));
    __VERIFIER_assert(!__builtin_isgreaterequal(1.0, (__builtin_nanf (""))));
    __VERIFIER_assert(!__builtin_isgreaterequal((__builtin_nanf ("")),1.0));

    __VERIFIER_assert(__builtin_isgreater(2.0, 1.0));
    __VERIFIER_assert(!__builtin_isgreater(1.0, 2.0));
    __VERIFIER_assert(!__builtin_isgreater(1.0, 1.0));
    __VERIFIER_assert(__builtin_isgreater((__builtin_inff ("")), 1.0));
    __VERIFIER_assert(!__builtin_isgreater(1.0, (__builtin_nanf (""))));
    __VERIFIER_assert(!__builtin_isgreater((__builtin_nanf ("")),1.0));
    
    __VERIFIER_assert(!__builtin_isless(2.0, 1.0));
    __VERIFIER_assert(__builtin_isless(1.0, 2.0));
    __VERIFIER_assert(!__builtin_isless(1.0, 1.0));
    __VERIFIER_assert(!__builtin_isless((__builtin_inff ("")), 1.0));
    __VERIFIER_assert(!__builtin_isless(1.0, (__builtin_nanf (""))));
    __VERIFIER_assert(!__builtin_isless((__builtin_nanf ("")),1.0));
    
    __VERIFIER_assert(!__builtin_islessequal(2.0, 1.0));
    __VERIFIER_assert(__builtin_islessequal(1.0, 2.0));
    __VERIFIER_assert(__builtin_islessequal(1.0, 1.0));
    __VERIFIER_assert(!__builtin_islessequal((__builtin_inff ("")), 1.0));
    __VERIFIER_assert(!__builtin_islessequal(1.0, (__builtin_nanf (""))));
    __VERIFIER_assert(!__builtin_islessequal((__builtin_nanf ("")),1.0));
    
    __VERIFIER_assert(!__builtin_isunordered(2.0, 1.0));
    __VERIFIER_assert(!__builtin_isunordered(1.0, 2.0));
    __VERIFIER_assert(!__builtin_isunordered(1.0, 1.0));
    __VERIFIER_assert(!__builtin_isunordered((__builtin_inff ("")), 1.0));
    __VERIFIER_assert(!__builtin_isunordered((__builtin_inff ("")), (__builtin_inff (""))));
    __VERIFIER_assert(__builtin_isunordered(1.0, (__builtin_nanf (""))));
    __VERIFIER_assert(__builtin_isunordered((__builtin_nanf ("")),1.0));
    __VERIFIER_assert(__builtin_isunordered((__builtin_nanf ("")),(__builtin_nanf (""))));
    
    __VERIFIER_assert(__builtin_islessgreater(2.0, 1.0));
    __VERIFIER_assert(__builtin_islessgreater(1.0, 2.0));
    __VERIFIER_assert(!__builtin_islessgreater(1.0, 1.0));
    __VERIFIER_assert(__builtin_islessgreater((__builtin_inff ("")), 1.0));
    __VERIFIER_assert(!__builtin_islessgreater((__builtin_inff ("")), (__builtin_inff (""))));
    __VERIFIER_assert(!__builtin_islessgreater(1.0, (__builtin_nanf (""))));
    __VERIFIER_assert(!__builtin_islessgreater((__builtin_nanf ("")),1.0));
    __VERIFIER_assert(!__builtin_islessgreater((__builtin_nanf ("")),(__builtin_nanf (""))));
    
    return 0;
}

