/* #Safe
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 08.02.2012
 * simple example where structs occur in loop invariant
 */

extern int __VERIFIER_nondet_int(void);

typedef struct {
	int fst;
	int snd;
} pair;

int main(void) {
	pair a = { .fst = 23, .snd = 42 };
	while (__VERIFIER_nondet_int()) {
		if (__VERIFIER_nondet_int()) {
			a.fst++;
			a.snd--;
		} else {
			a.fst--;
			a.snd++;
		}
	}
	//@ assert a.fst+a.snd >= 0;
	return 0;
}