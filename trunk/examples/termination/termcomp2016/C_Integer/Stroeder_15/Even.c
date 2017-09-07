//#termcomp16-someonesaidno
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
    int b;
    i = __VERIFIER_nondet_int();
    
    while (i != 1 && i != 0) {
        i = i-2;
    }
    
    return 0;
}
