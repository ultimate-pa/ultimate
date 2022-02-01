//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int c;
    int x, y, z;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    z = __VERIFIER_nondet_int();
    c = 0;
    while (x > z) {
        while (y > z) {
            y = y - 1;
            c = c + 1;
        }
        c = c + 1;
        x = x - 1;
    }
    return 0;
}
