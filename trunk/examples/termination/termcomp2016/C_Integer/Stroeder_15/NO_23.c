//#termcomp16-someonesaidno
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
    i = 0;
    
    while (i < 100) {
        if (i < 50) { i = 51; }
        else { i = 49; }
    }
    
    return 0;
}
