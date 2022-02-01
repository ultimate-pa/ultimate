/*
 * Implementation of bubble sort algorithm.
 * Date: 2014-07-16
 * Author: heizmann@informatik.uni-freiburg.de
 */

extern int __VERIFIER_nondet_int(void);

void bubblesort(int a[], int i) {
    while (i>=0) {
        int j = 0;
        while (j < i) {
            if (a[j] > a[i]) {
                int tmp = a[i];
                a[i] = a[j];
                a[j] = tmp;
            }
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
    int a[n];
    bubblesort(a,n-1);
}

