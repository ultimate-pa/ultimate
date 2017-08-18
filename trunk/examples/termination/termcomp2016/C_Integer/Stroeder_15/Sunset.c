//#termcomp16-someonesaidno
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
    i = __VERIFIER_nondet_int();
    
    while (i > 10) {
        if (i == 25) {
            i = 30;
        }
        if (i <= 30) {
            i = i-1;
        } else {
            i = 20;
        }
    }
    
    return 0;
}
