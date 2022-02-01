extern void __VERIFIER_error() __attribute__ ((__noreturn__));

/*
 * In some setting and only after some interation we can detect (with -ea)
 * that there is a bug in the sequential composition with pendings calls.
 * 
 * Date: 2016-12-03
 * Author: Matthias Heizmann
 * 
 * 
 */

extern int __VERIFIER_nondet_int(void);

unsigned int isOdd(unsigned int n);
unsigned int isEven(unsigned int n);

unsigned int isOdd(unsigned int n) {
    if (n == 0) {
        return 0;
    } else if (n == 1) {
        return 1;
    } else {
        return isEven(n - 1);
    }
}

unsigned int isEven(unsigned int n) {
    if (n == 0) {
        return 1;
    } else if (n == 1) {
        return 0;
    } else {
        return isOdd(n - 1);
    }
}


unsigned int main() {
    unsigned int n = __VERIFIER_nondet_int();
    unsigned int result = isEven(n);
    unsigned int mod = n % 2;
    if (result < 0 || result == mod) {
        return 0;
    } else {
        ERROR: __VERIFIER_error();
    }
}
