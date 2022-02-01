//#Terminating
/*
 * In r11928 the C2Boogie translation constructed the label Loop~3 twice and
 * therefore this program was wrongly considered nonterminating.
 *
 * Date: 2014-06-30
 * Author: Matthias Heizmann
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int x = __VERIFIER_nondet_int();
	int y;
	while (x >= 42) {
		while (0)
			y = 23;
		x = 2;
		while (0)
			y = 23;
	}
	return 0;
}