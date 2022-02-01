 
extern int __VERIFIER_nondet_int(void);


void swap(int a[], int i, int j) {
    int tmp = a[i];
    a[i] = a[j];
    a[j] = tmp;
}

void bubblesort(int a[], int i) {
    while (i>=0) {
        int j = 0;
        while (j < i) {
//            if (a[j] > a[i]) {
                swap(a,i,j);
//            }
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
    int *a = malloc(n * sizeof(int));
    bubblesort(a,n-1);
}

