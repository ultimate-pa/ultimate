//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int c, i, j;
    i = __VERIFIER_nondet_int();
    j = __VERIFIER_nondet_int();
    c = 0;
    while (i >= 0) {
        j = 0;
        while (j <= i - 1) {
            j = j + 1;
            c = c + 1;
        }
        i = i - 1;
    }
    return 0;
}
