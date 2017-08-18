//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int c, x, y;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    c = 0;
    while (x >= 0) {
        y = 1;
        while (x > y) {
            y = 2*y;
            c = c + 1;
        }
        x = x - 1;
    }
    return 0;
}
