//#termcomp16-someonesaidyes
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x;
    int y;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    
    while (x == y && x > 0) {
        while (y > 0) {
            x = x-1;
            y = y-1;
        }
    }
    
    return 0;
}
