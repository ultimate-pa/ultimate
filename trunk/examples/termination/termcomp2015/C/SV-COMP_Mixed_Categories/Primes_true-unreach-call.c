extern void __VERIFIER_error() __attribute__ ((__noreturn__));

/*
 * Recursive implementation of prime number test
 * (Sieve of Eratosthenes)
 * 
 * Author: Jan Leike
 * Date: 2013-07-17
 * 
 */

extern int __VERIFIER_nondet_int(void);

// Multiplies two integers n and m
int mult(int n, int m) {
    if (m < 0) {
        return mult(n, -m);
    }
    if (m == 0) {
        return 0;
    }
    if (m == 1) {
        return 1;
    }
    return n + mult(n, m - 1);
}

// Is n a multiple of m?
int multiple_of(int n, int m) {
    if (m < 0) {
        return multiple_of(n, -m);
    }
    if (n < 0) {
        return multiple_of(-n, m); // false
    }
    if (m == 0) {
        return 0; // false
    }
    if (n == 0) {
        return 1; // true
    }
    return multiple_of(n - m, m);
}


int is_prime_(int n, int m);
int is_prime(int n);

// Is n prime?
int is_prime(int n) {
    return is_prime_(n, n - 1);
}


int is_prime_(int n, int m) {
    if (n <= 1) {
        return 0; // false
    }
    if (n == 2) {
        return 1; // true
    }
    if (n > 2) {
        if (m <= 1) {
            return 1; // true
        } else {
            if (multiple_of(n, m) == 0) {
                return 0; // false
            }
            return is_prime_(n, m - 1);
        }
    }
}

int main() {
    int n = __VERIFIER_nondet_int();
    if (n < 1 || n > 46340) {
        return 0;
    }
    int result = is_prime(n);
    int f1 = __VERIFIER_nondet_int();
    if (f1 < 1 || f1 > 46340) {
        return 0;
    }
    int f2 = __VERIFIER_nondet_int();
    if (f1 < 1 || f1 > 46340) {
        return 0;
    }

    if (result == 1 && mult(f1, f2) == n && f1 > 1 && f2 > 1) {
        ERROR: __VERIFIER_error();
    } else {
        return 0;
    }
}
