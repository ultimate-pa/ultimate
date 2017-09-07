//#termcomp16-someonesaidno
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
    int range;
    i = __VERIFIER_nondet_int();
    range = 20;
    
    while (-range <= i && i <= range) {
        if (range-i < 5 || range+i < 5) {
            i = i*(-1);
        } else {
            range = range+1;
            i = i-1;
            if (i == 0) {
                range = -1;
            }
        }
    }
    
    return 0;
}
