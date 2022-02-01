//#Unsafe
/*
 * 2020-04-23
 * Delta-debugged example from recursive/recHanoi03-2.c
 * For IsEmptyHeuristic: AssertionError: IsEmptyHeuristic did not match IsEmpty
 * 
 * Author: dietsch@cs.uni-freiburg.de
 */

int hanoi(int n) {
    if (n == 0) {
                return 0;
        }
        return      hanoi(n-1)     ;
}

void main() {
    int n  ;

      hanoi(n);
    if (1 >= n) ; else {
        ERROR: __VERIFIER_error();
    }
}
