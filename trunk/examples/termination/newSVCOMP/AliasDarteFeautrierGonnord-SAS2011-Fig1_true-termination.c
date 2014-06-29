/*
 * Program from Figure 1 of
 * 2011SAS - Alias, Darte, Feautrier, Gonnord - Multi-dimensional Rankings, Program Termination, and Complexity Bounds of Flowchart Programs
 *
 * Date: 2014-06-29
 * Author: Jan Leike
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int m = __VERIFIER_nondet_int();
	int y = 0;
	int x = m;
	while (x >= 0 && y >= 0) {
		if (__VERIFIER_nondet_int()) {
			while (y <= m && __VERIFIER_nondet_int()) {
				y++;
			}
			x--;
		}
		y--;
	}
	return 0;
}
