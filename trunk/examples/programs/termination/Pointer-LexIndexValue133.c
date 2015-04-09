//#rTerminationDerivable
/*
 * Date: 2012-06-03
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * 2-lex ranking function: f(k, *p) = (k, *p)
 * 
 * We submitted the very similar program
 *     termination-crafted/SyntaxSupportPointer01_true-termination.c
 * to the SV-COMP
 *
 */

extern int __VERIFIER_nondet_int();

int main() {
    int* p = malloc(133 * sizeof(int));
    int k = 133;
    while (*p >= 0 && k >= 0) {
        if (__VERIFIER_nondet_int()) {
			k--;
		} else {
			(*p)--;
		}
    }
    free(p);
    return 0;
}