//#termcomp16-someonesaidyes
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x;
    int y;
    x = __VERIFIER_nondet_int();
    
    while (x > 0) {
        y = 0;
        while (y < x) {
            y = y+1;
        }
        x = x-1;
    }
    
    return 0;
}
