/*
 * Recursive implementation multiplication by repeated addition
 * 
 * Author: Jan Leike
 * Date: 2013-07-17
 * 
 */

extern int __VERIFIER_nondet_int(void);

// Multiplies two integers n and m
int mult(int n, int m) {
    if (m < 0) {
        return -1 * mult(n, -m);
    }
    if (m == 0) {
        return 0;
    }
    return n + mult(n, m - 1);
}

int main() {
    int m = __VERIFIER_nondet_int();
    int n = __VERIFIER_nondet_int();
    int res = mult(m, n);
    return 0;
}
