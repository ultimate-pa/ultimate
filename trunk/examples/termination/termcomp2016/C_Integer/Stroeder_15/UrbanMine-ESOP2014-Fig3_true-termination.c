//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
/*
 * Program from Fig.3 of
 * 2014ESOP - Urban,Miné - An Abstract Domain to Infer Ordinal-Valued Ranking Functions
 *
 * Date: 2014
 * Author: Caterina Urban
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
	int x;
	int y;
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
	while (x != 0 && y > 0) {
	    if (x > 0) {
		    if (__VERIFIER_nondet_int() != 0) {
			    x = x - 1;
				y = __VERIFIER_nondet_int();
			} else {
			    y = y - 1;
			}
		} else {
		    if (__VERIFIER_nondet_int() != 0) {
			    x = x + 1;
			} else {
			    y = y - 1;
				x = __VERIFIER_nondet_int();
			}		
		}
	}
    return 0;
}
