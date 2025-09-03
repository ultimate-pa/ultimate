//#Unsafe
// Author: @Costandre97
// Date: 2025-09-02
//
// Triggered a bug in the parallel composition of transformulas when analysed with "Size of a code block=LoopFreeBlock".
// See issue #746.

extern unsigned int __VERIFIER_nondet_uint(void);
int main(void) {
        unsigned int x = 1;
        if(x > 0) {x = __VERIFIER_nondet_uint();}
        if(x == 2) __VERIFIER_error();
}
