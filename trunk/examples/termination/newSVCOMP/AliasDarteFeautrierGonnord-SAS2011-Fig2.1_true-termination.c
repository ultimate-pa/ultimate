/*
 * First program from Figure 2 of
 * 2011SAS - Alias, Darte, Feautrier, Gonnord - Multi-dimensional Rankings, Program Termination, and Complexity Bounds of Flowchart Programs
 *
 * Date: 2014-06-29
 * Author: Jan Leike
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int m = __VERIFIER_nondet_int();
	int x = m;
	int y = m;
	while (x >= 2) {
		x--;
		y = y + x;
		while (y >= x && __VERIFIER_nondet_int()) {
			y--;
		}
		x--;
		y = y - x;
	}
	return 0;
}
