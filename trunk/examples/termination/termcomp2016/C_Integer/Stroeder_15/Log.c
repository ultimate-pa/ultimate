//#termcomp16-someonesaidyes
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x;
    int xtmp;
    int res;
    int restmp;
    x = __VERIFIER_nondet_int();
    res = 0;
    
    while (x > 1) {
        xtmp = x;
        restmp = 0;
        
        while (xtmp > 1) {
            xtmp = xtmp-2;
            restmp = restmp+1;
        }
        
        x = xtmp;
        res = res+1;
        
    }
    
    return 0;
}
