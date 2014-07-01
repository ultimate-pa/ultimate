/*
 * Program depicted in Fig.8b of
 * 2013TACAS - Cook,See,Zuleger - Ramsey vs. Lexicographic Termination Proving
 *
 * Date: 2014
 * Author: Caterina Urban
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int x = __VERIFIER_nondet_int();
	int M = __VERIFIER_nondet_int();
	if (M > 0) {
		while (x != M) {
			if (x > M)
				x = 0;
			else
				x = x + 1;
		}
	}
	return 0;
}