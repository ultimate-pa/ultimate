//#termcomp16-someonesaidyes
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x;
    int y;
    int random;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    
    while (x > 0 && y > 0) {
        random = __VERIFIER_nondet_int();
        if (random < 42) {
            x = x-1;
            random = __VERIFIER_nondet_int();
            y = random;
        } else {
            y = y-1;
        }
    }
    
    return 0;
}
