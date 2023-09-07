extern void reach_error(void);
extern int __VERIFIER_nondet_int(void);

int myFunc() {
    int p = 42;
    int n = __VERIFIER_nondet_int();
    //@ loop invariant p != 0 || n == -1;
    while ( n>=0 ) {
        if (p == 0) {
            reach_error();
        }
        if (n == 0) {
            p = 0;
        }
        n--;
    }
    return 0;
}
