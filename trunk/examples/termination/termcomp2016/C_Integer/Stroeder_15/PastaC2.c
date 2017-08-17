//#termcomp16-someonesaidyes
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x;
    int y;
    x = __VERIFIER_nondet_int();
    
    while (x >= 0) {
        x = x+1;
        y = 1;
        while (x >= y) {
            y = y+1;
        }
        x = x-2;
    }
    
    return 0;
}
