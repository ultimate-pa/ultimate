/*
 * Program from Fig.1 of
 * 2001TACAS - Colon,Sipma - Synthesis of Linear Ranking Functions
 *
 * Date: 2014-06-21
 * Author: Caterina Urban, Matthias Heizmann
 *
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int k = __VERIFIER_nondet_int();
    int i = __VERIFIER_nondet_int();
    int j = __VERIFIER_nondet_int();
	while (i <= 100 && j <= k) {
		int tmp = i;
		i = j;
		j = tmp + 1;
		k = k - 1;
	}
	return 0;
}