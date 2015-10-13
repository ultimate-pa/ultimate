/*
 * Program from Example 7 of
 * 2014TACAS - Leike, Heizmann - Ranking Templates for Linear Loops
 * 
 * In the conference version of this paper, the authors claimed that this
 * lasso program does not have a multiphase ranking function. However, this
 * lasso program has the following 2-phase ranking function.
 *     f_0(x, y) = 2q + z
 *     f_1(x, y) = q
 * The authors thank Samir Genaim for pointing out this error in their paper.
 *
 * Date: 2014-06-29
 * Author: Jan Leike
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int q = __VERIFIER_nondet_int();
	int z = __VERIFIER_nondet_int();
	while (q > 0) {
		q = q + z - 1;
		z = -z;
	}
	return 0;
}
