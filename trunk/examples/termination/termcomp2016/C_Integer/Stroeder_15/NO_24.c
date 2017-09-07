//#termcomp16-someonesaidno
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int a;
    int b;
    a = 1;
    b = 2;
    
    while (a + b < 5) {
        a = a - b;
        b = a + b;
        a = b - a;
    }
    
    return 0;
}
