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


