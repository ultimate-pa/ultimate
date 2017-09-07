//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int c, i, j, k, tmp;
    i = __VERIFIER_nondet_int();
    j = __VERIFIER_nondet_int();
    k = __VERIFIER_nondet_int();
    tmp = __VERIFIER_nondet_int();
    c = 0;
    while ((i <= 100) && (j <= k)) {
        tmp = i;
        i = j;
        j = tmp + 1;
        k = k - 1;
        c = c + 1;
    }
    return 0;
}
