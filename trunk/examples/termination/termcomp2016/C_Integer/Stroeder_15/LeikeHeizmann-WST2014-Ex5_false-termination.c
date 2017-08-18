//#termcomp16-someonesaidno
/*
 * Program from Example 5 of
 * 2014WST - Leike, Heizmann - Geometric Series as Nontermination Arguments for Linear Lasso Programs
 *
 * Date: 2014-06-29
 * Author: Jan Leike
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int a, b, olda;
	a = __VERIFIER_nondet_int();
	b = __VERIFIER_nondet_int();
	while (a >= 7) {
		olda = a;
		a = b;
		b = olda + 1;
		// b = a + 1; is a typo in the paper
	}
	return 0;
}
