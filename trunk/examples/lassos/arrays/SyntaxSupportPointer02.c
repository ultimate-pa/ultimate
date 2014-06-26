//#rTerminationDerivable
/*
 * Date: 2012-06-03
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * 2-lex ranking function: f(k, *p) = (k, *p)
 *
 */

extern int __VERIFIER_nondet_int();

int main() {
    int *p = malloc(133 * sizeof(int));
    while (*p >= 0) {
		(*p)--;
	}
    return 0;
}