//#termcomp16-someonesaidyes
extern void __VERIFIER_error() __attribute__ ((__noreturn__));

/*
 * Recursive implementation integer addition.
 * 
 * Author: Matthias Heizmann
 * Date: 2013-07-13
 * 
 */

extern int __VERIFIER_nondet_int(void);

int addition(int m, int n) {
    if (n == 0) {
        return m;
    }
    if (n > 0) {
        return addition(m+1, n-1);
    }
    if (n < 0) {
        return addition(m-1, n+1);
    }
}


int main() {
    int m = __VERIFIER_nondet_int();
    if (m < 0 || m > 2147483647) {
        return 0;
    }
    int n = __VERIFIER_nondet_int();
    if (n < 0 || n > 2147483647) {
        return 0;
    }
    int result = addition(m,n);
    if (result == m + n) {
        return 0;
    } else {
        ERROR: __VERIFIER_error();
    }
}
