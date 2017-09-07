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
    
    while (x > y) {
        y = x+1;
        res = res+1;
    }
    
    return 0;
}

