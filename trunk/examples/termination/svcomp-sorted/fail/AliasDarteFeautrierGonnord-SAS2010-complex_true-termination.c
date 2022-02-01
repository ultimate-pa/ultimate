/*
 * Program used in the experimental evaluation of the following paper.
 * 2010SAS - Alias,Darte,Feautrier,Gonnord, Multi-dimensional Rankings, Program Termination, and Complexity Bounds of Flowchart Programs
 *
 * Date: 2014
 * Author: Caterina Urban
 */
extern int __VERIFIER_nondet_int(void);

int main() {
	int a = __VERIFIER_nondet_int();
	int b = __VERIFIER_nondet_int();
	while (a < 30) {
		while (b < a) {
			if (b > 5)
				b = b + 7;
			else
				b = b + 2;
			if (b >= 10 && b <= 12)
				a = a + 10;
			else
				a = a + 1;
		}
		a = a + 2;
		b = b - 10;
	}
	return 0;
}