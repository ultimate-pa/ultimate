//#termcomp16-someonesaidyes
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x;
    int y;
    int z;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    z = __VERIFIER_nondet_int();
    
    while (x < y) {
        if (x < z) {
            x = x+1;
        } else {
            z = z+1;
        }
    }
    
    return 0;
}
