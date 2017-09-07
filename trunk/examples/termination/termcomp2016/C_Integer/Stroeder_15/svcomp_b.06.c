//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int c;
    int x, y;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    c = 0;
    while ((x > 0) && (y > 0)) {
        x = x - 1;
        y = y - 1;
        c = c + 1;
    }
    return 0;
}
