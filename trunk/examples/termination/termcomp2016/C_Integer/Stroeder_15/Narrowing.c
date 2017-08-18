//#termcomp16-someonesaidno
typedef enum { false, true } bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
    int range;
    int up;
    i = __VERIFIER_nondet_int();
    range = 20;
    up = 0;
    
    while (0 <= i && i <= range) {
        if (i == 0) {
            up = 1;
        }
        if (i == range) {
            up = 0;
        }
        if (up == 1) {
            i = i+1;
        }
        if (up == 0) {
            i = i-1;
        }
        if (i == range-2) {
            range = range-1;
        }
    }
    
    return 0;
}
