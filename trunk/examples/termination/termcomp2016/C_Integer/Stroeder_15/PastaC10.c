//#termcomp16-someonesaidno
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
    int j;
    int r;
    i = __VERIFIER_nondet_int();
    j = __VERIFIER_nondet_int();
    
    while (i - j >= 1) {
        i = i - __VERIFIER_nondet_int();
        r = __VERIFIER_nondet_int() + 1;
        j = j + r;
    }
    
    return 0;
}
