//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
/*
 * Program from Example 9 of
 * 2014TACAS - Leike, Heizmann - Ranking Templates for Linear Loops
 *
 * Date: 2014-06-29
 * Author: Jan Leike
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int p, q;
	q = __VERIFIER_nondet_int();
	p = __VERIFIER_nondet_int();
	while (q > 0 && p > 0 && p != q) {
		if (q < p) {
			q = q - 1;
		} else {
			if (p < q) {
				p = p - 1;
			}
		}
	}
	return 0;
}
