//#termcomp16-someonesaidyes
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x;
    int y;
    int t;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    
    while (x > y) {
        t = x;
        x = y;
        y = t;
    }
    
    return 0;
}
