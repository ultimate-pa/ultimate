/*
 * Implementation of bubble sort algorithm. All statements that are not relevant
 * for termination have been removed.
 * Date: 2014-07-16
 * Author: heizmann@informatik.uni-freiburg.de
 */

extern int __VERIFIER_nondet_int(void);


void bubblesort(int i) {
    while (i>=0) {
        int j = 0;
        while (j < i) {
            j++;
        }
        i--;
    }
}

int main() {
    int n = __VERIFIER_nondet_int();
    if (n < 1) {
        n = 1;
    }
    bubblesort(n-1);
}


