/*
 * Program depicted in Fig.8a of
 * 2013TACAS - Cook,See,Zuleger - Ramsey vs. Lexicographic Termination Proving
 *
 * Date: 2014
 * Author: Caterina Urban
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int x = __VERIFIER_nondet_int();
	while (x != 0) {
		if (x > 0) {
			x = x - 1;
		} else {
			x = x + 1;
		}
	}
	return 0;
}