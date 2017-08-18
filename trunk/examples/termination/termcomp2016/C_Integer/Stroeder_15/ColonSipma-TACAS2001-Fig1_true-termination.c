//#termcomp16-someonesaidyes
/*
 * Program from Fig.1 of
 * 2001TACAS - Colon,Sipma - Synthesis of Linear Ranking Functions
 *
 * Date: 2014-06-21
 * Author: Caterina Urban, Matthias Heizmann
 *
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int k, i, j, tmp;
	k = __VERIFIER_nondet_int();
    i = __VERIFIER_nondet_int();
    j = __VERIFIER_nondet_int();
	while (i <= 100 && j <= k) {
		tmp = i;
		i = j;
		j = tmp + 1;
		k = k - 1;
	}
	return 0;
}