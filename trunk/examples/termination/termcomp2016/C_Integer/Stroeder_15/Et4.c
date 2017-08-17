//#termcomp16-someonesaidno
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int a;
    int b;
    int c;
    int r;
    a = __VERIFIER_nondet_int();
    b = __VERIFIER_nondet_int();
    c = __VERIFIER_nondet_int();
    
    while ( (b - c >= 1) && (a == c)) {
        r = __VERIFIER_nondet_int();
        b = 10;
        c = c + 1 + r;
        a = c;
    }
    
    return 0;
}
