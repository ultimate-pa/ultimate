/*
  Cohen's integer division
  returns x % y
  http://www.cs.upc.edu/~erodri/webpage/polynomial_invariants/cohendiv.htm
*/
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "cohendiv-ll.c", 8, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
void __VERIFIER_assert(int cond) {
    if (!(cond)) {
    ERROR:
	{reach_error();}
    }
    return;
}

int main() {
    int x, y;
    long long q, r, a, b;

    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();

    assume_abort_if_not(y >= 1);

    q = 0;
    r = x;
    a = 0;
    b = 0;

    while (1) {
	__VERIFIER_assert(b == y*a);
	__VERIFIER_assert(x == q*y + r);
    
	if (!(r >= y))
	    break;
	a = 1;
	b = y;

	while (1) {            
	    __VERIFIER_assert(b == y*a);
	    __VERIFIER_assert(x == q*y + r);
	    __VERIFIER_assert(r >= 0);

	    if (!(r >= 2 * b))
		break;
	    
	    __VERIFIER_assert(r >= 2 * y * a);
	    
	    a = 2 * a;
	    b = 2 * b;
	}
	r = r - b;
	q = q + a;
    }
    
    __VERIFIER_assert(x == q*y + r);
    return 0;
}
