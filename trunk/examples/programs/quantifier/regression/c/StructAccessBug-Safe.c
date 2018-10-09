/* #Safe
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2018-10-04
 * Triggers probably a bug in the quantifier elimination for arrays.
 * Reproducible only without inlining.
 */

extern int __VERIFIER_nondet_int(void);

typedef struct {
	int fst;
	int snd;
} pair;

int main(void) {
	pair a = { .fst = 23, .snd = 42 };
	a.fst = a.fst;
	//@ assert a.fst >= 0;
	return 0;
}
