/*
 * Program from Example 7 of
 * 2014TACAS - Leike, Heizmann - Ranking Templates for Linear Loops
 *
 * Date: 2014-06-29
 * Author: Jan Leike
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int q = __VERIFIER_nondet_int();
	int z = __VERIFIER_nondet_int();
	while (q > 0) {
		q = q + z - 1;
		z = -z;
	}
	return 0;
}
