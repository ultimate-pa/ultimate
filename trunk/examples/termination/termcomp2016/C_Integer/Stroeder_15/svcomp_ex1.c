//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x, y, r;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    r = 1;
    while (y > 0) {
        r = r*x;
        y = y - 1;
    }
    return 0;
}
