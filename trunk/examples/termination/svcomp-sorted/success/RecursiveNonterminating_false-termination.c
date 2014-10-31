/*
 * Author: Matthias Heizmann
 * Date: 2014-06-29
 * 
 */

extern int __VERIFIER_nondet_int(void);


void rec(int x, int y) {
	if (x <= 23 && x >= -42) {
		rec(2*y-2, x + 1);
	}
}

int main() {
    int n = __VERIFIER_nondet_int();
    rec(n, n + 1);
    return 0;
}
