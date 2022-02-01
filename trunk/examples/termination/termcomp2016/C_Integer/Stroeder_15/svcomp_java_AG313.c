//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i, x, y;
    i = 0;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    if (x!=0) {
        while (x > 0 && y > 0) {
            i = i + 1;
            x = (x - 1)- (y - 1);
        }
    }
    return 0;
}
