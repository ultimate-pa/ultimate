//#termcomp16-someonesaidyes
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x;
    int y;
    int res;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    res = 0;
    
    while (x > 0 && y > 0) {
        x = x-1;
        y = y-1;
    }
    
    while (x > 0) {
        y = y+1;
        res = res+1;
        while (x > 0 && y > 0) {
            x = x-1;
            y = y-1;
        }
    }
    
    return 0;
}
