//#termcomp16-someonesaidno
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
    i = 0;
    
    while (i < 100) {
        if (i < 50) { i = i+1; }
        else { i = i-1; }
    }
    
    return 0;
}
