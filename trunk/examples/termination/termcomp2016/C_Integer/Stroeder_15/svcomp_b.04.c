//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x, y, tmp;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    tmp = __VERIFIER_nondet_int();
    while (x > y) {
        tmp = x;
        x = y;
        y = tmp;
    }
    return 0;
}
