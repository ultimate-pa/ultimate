extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "test_locks_5.c", 3, "reach_error"); }

extern int __VERIFIER_nondet_int();
int main()
{
    int p1 = __VERIFIER_nondet_int();  // condition variable
    int lk1; // lock variable

    int p2 = __VERIFIER_nondet_int();  // condition variable
    int lk2; // lock variable

    int p3 = __VERIFIER_nondet_int();  // condition variable
    int lk3; // lock variable

    int p4 = __VERIFIER_nondet_int();  // condition variable
    int lk4; // lock variable

    int p5 = __VERIFIER_nondet_int();  // condition variable
    int lk5; // lock variable


    int cond;

    while(1) {
        cond = __VERIFIER_nondet_int();
        if (cond == 0) {
            goto out;
        } else {}
        lk1 = 0; // initially lock is open

        lk2 = 0; // initially lock is open

        lk3 = 0; // initially lock is open

        lk4 = 0; // initially lock is open

        lk5 = 0; // initially lock is open


    // lock phase
        if (p1 != 0) {
            lk1 = 1; // acquire lock
        } else {}

        if (p2 != 0) {
            lk2 = 1; // acquire lock
        } else {}

        if (p3 != 0) {
            lk3 = 1; // acquire lock
        } else {}

        if (p4 != 0) {
            lk4 = 1; // acquire lock
        } else {}

        if (p5 != 0) {
            lk5 = 1; // acquire lock
        } else {}


    // unlock phase
        if (p1 != 0) {
            if (lk1 != 1) goto ERROR; // assertion failure
            lk1 = 0;
        } else {}

        if (p2 != 0) {
            if (lk2 != 1) goto ERROR; // assertion failure
            lk2 = 0;
        } else {}

        if (p3 != 0) {
            if (lk3 != 1) goto ERROR; // assertion failure
            lk3 = 0;
        } else {}

        if (p4 != 0) {
            if (lk4 != 1) goto ERROR; // assertion failure
            lk4 = 0;
        } else {}

        if (p5 != 0) {
            if (lk5 != 1) goto ERROR; // assertion failure
            lk5 = 0;
        } else {}

    }
  out:
    return 0;
  ERROR: {reach_error();abort();}
    return 0;  
}

