/*
 * Program from Table 1 of
 * 2006FLOPS - James Avery - Size-Change Termination and Bound Analysis
 *
 * Date: 18.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int(void);

int subxy(int x, int y) {
	int z,i;
	z = 0;
	i = x;
	if (y <= 0 || x <= 0) {
		return 0;
	}
	while (i > 0) {
		i--;
		z++;
	}
	while (i < y) {
		i++;
		z--;
	}
	return z;
}

int main() {
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	subxy(x,y);
	return 0;
}
