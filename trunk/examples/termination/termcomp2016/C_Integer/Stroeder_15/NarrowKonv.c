//#termcomp16-someonesaidno
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
    int range;
    i = __VERIFIER_nondet_int();
    range = 20;
    
    while (0 <= i && i <= range) {
        if (!(0 == i && i == range)) {
            if (i == range) {
                i = 0;
                range = range-1;
            } else {
                i = i+1;
            }
        }
    }
    
    return 0;
}
