extern void __VERIFIER_error() __attribute__ ((__noreturn__));

/*
 * Recursive implementation integer addition.
 * 
 * Author: Matthias Heizmann
 * Date: 2013-07-13
 * 
 */

extern int __VERIFIER_nondet_int(void);

int isOdd(int n);
int isEven(int n);

int isOdd(int n) {
    if (n == 0) {
        return 0;
    } else if (n == 1) {
        return 1;
    } else {
        return isEven(n - 1);
    }
}

int isEven(int n) {
    if (n == 0) {
        return 1;
    } else if (n == 1) {
        return 0;
    } else {
        return isOdd(n - 1);
    }
}


int main() {
    int n = __VERIFIER_nondet_int();
    if (n < 0) {
        return 0;
    }
    int result = isOdd(n);
    int mod = n % 2;
    if (result < 0 || result == mod) {
        return 0;
    } else {
        ERROR: __VERIFIER_error();
    }
}
