/*
 * Program from Fig.1 of
 * 2013CAV - Brockschmidt,Cook,Fuhs - Better termination proving through cooperation -draft
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int(void);


int main() {
	int i,j, n;
	while (i < n) {
		j = 0;
		while (j <= i) {
			j = j + 1;
		}
		i = i + 1;
	}
	return 0;
}


