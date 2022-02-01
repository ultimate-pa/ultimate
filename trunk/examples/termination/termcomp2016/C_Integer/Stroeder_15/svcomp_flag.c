//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int flag;
    int c, x, y;
    flag = 1;
    c = 0;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    while (flag != 0) {
        if (x >= y) {
            flag = 0;
        }
        x = x + 1;
        c = c + 1;
    }
    return 0;
}
