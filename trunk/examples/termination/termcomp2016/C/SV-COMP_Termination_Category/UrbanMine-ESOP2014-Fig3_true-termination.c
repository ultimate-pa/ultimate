/*
 * Program from Fig.3 of
 * 2014ESOP - Urban,Miné - An Abstract Domain to Infer Ordinal-Valued Ranking Functions
 *
 * Date: 2014
 * Author: Caterina Urban
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	while (x != 0 && y > 0) {
	    if (x > 0) {
		    if (__VERIFIER_nondet_int()) {
			    x = x - 1;
				y = __VERIFIER_nondet_int();
			} else {
			    y = y - 1;
			}
		} else {
		    if (__VERIFIER_nondet_int()) {
			    x = x + 1;
			} else {
			    y = y - 1;
				x = __VERIFIER_nondet_int();
			}		
		}
	}
}