//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
/*
 * Program from Fig.3 of
 * 2013TACAS - Cook,See,Zuleger - Ramsey vs. Lexicographic Termination Proving
 *
 * Date: 8.6.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x, y;
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
    while (x>0 && y>0) {
        if (__VERIFIER_nondet_int() != 0) {
            x = x - 1;
        } else {
            x = __VERIFIER_nondet_int();
            y = y - 1;
        }
    }
    return 0;
}
