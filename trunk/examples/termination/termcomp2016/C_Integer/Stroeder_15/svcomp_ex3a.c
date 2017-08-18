//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int c, x;
    x = __VERIFIER_nondet_int();
    c = 0;
    while ((x > 1) && (x < 100)) {
        x = x*x;
        c = c + 1;
    }
    return 0;
}
