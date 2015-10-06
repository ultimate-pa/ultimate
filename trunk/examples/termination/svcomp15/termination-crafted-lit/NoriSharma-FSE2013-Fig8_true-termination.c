/*
 * Program from Fig.8 of
 * 2013FSE - Nori,Sharma - Termination Proofs from Tests
 *
 * Date: 18.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	int z = __VERIFIER_nondet_int();
    int u,v,w,c;
    u = x;
    v = y;
    w = z;
    c = 0;
    while (x >= y) {
    	c = c + 1;
    	if (z > 1) {
    		z = z - 1;
    		x = x + z;
    	} else {
    		y = y + 1;
    	}
    }
}
