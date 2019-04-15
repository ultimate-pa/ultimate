//#Safe
/*
 * 
 * Date: 2019-04-12
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * 
 */
extern int __VERIFIER_nondet_int(void);
extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int main(void) {
    unsigned int x = 1;
    unsigned int y = 1;
    while(x <= 256*256*256*255) {
        if (__VERIFIER_nondet_int()) {
            x = 3 * x;
            y = -2 * y + 1;
        } else {
            unsigned int tmp = x;
            x = y;
            y = tmp;
        }
    }
    if (y == 0) {
        __VERIFIER_error();
    }
    return 0;
}

