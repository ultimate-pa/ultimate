//#Safe
/*
 * 2017-11-24 DD
 * 
 * https://gcc.gnu.org/onlinedocs/gcc/Other-Builtins.html see for __builtin_expect()
 *
 * Built-in Function: long __builtin_expect (long exp, long c)
 *
 * You may use __builtin_expect to provide the compiler with branch prediction information. In general, you
 * should prefer to use actual profile feedback for this (-fprofile-arcs), as programmers are notoriously bad at
 * predicting how their programs actually perform. However, there are applications in which this data is hard to
 * collect.
 *
 * The return value is the value of exp, which should be an integral expression. The semantics of the built-in
 * are that it is expected that exp == c. For example:
 *
 * <code>if (__builtin_expect (x, 0)) foo ();</code>
 *
 * indicates that we do not expect to call foo, since we expect x to be zero. Since you are limited to integral
 * expressions for exp, you should use constructions such as
 *
 * <code>if (__builtin_expect (ptr != NULL, 1)) foo (*ptr);</code>
 *
 * when testing pointer or floating-point values.
 
 */
 
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
 
void main() 
{ 
    int x = 0;
    int y = 1;
    
    if(__builtin_expect(x,y)){
        __VERIFIER_error();    
    }
    
    if(!(__builtin_expect(y,x))){
        __VERIFIER_error();    
    }
}