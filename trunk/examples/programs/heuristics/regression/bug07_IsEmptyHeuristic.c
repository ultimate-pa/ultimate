//#Safe
/*
 * 2020-04-23
 * Delta-debugged example from recursive/recHanoi01.c
 * For IsEmptyHeuristic: AssertionError: IsEmptyHeuristic did not match IsEmpty
 * 
 * Author: dietsch@cs.uni-freiburg.de
 */

int counter;

void applyHanoi(int n, int from, int to, int via)
{
        if (n == 0) {
                return;
        }

        counter++;
        applyHanoi(n-1, 0, 0, 0);

}

void main() {
    int n  ;

    applyHanoi(n, 0, 0, 0);
    int result =   n ;

    if (result == counter) ; else {
        ERROR: __VERIFIER_error();
    }
}


