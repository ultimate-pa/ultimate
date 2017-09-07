//#termcomp16-someonesaidno
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int a;
    int b;
    int r;
    a = __VERIFIER_nondet_int();
    b = __VERIFIER_nondet_int();
    
    while (b > 0) {
        r =  __VERIFIER_nondet_int();
        b = a - 1 - r;
        a = a - 1 - r;
    }
    
    return 0;
}