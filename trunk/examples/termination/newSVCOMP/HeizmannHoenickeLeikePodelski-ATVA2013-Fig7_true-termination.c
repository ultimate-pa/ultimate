/*
 * Program from Figure 7 of
 * 2013ATVA - Heizmann, Hoenicke, Leike, Podelski - Linear Ranking for Linear Lasso Programs
 *
 * Date: 2014-06-29
 * Author: Jan Leike
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int a_length = __VERIFIER_nondet_int();
	if (a_length <  1) {
		return 0;
	}
	int a[a_length];
	int offset = 1;
	int i = 0;
	while (i < a_length) {
		if (a[i] < 0) {
			break;
		}
		i = i + offset + a[i];
	}
	return 0;
}
