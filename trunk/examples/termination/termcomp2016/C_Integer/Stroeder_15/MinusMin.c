//#termcomp16-someonesaidyes
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x;
    int y;
    int res;
    int min;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    res = 0;
    
    if (x < y) { min = x; }
    else { min = y; }
    
    while (min == y) {
        y = y+1;
        res = res+1;
        if (x < y) { min = x; }
        else { min = y; }
    }
    
    return 0;
}
