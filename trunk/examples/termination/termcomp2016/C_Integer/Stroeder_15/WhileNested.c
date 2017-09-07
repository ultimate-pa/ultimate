//#termcomp16-someonesaidno
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
    int j;
    i = __VERIFIER_nondet_int();
    
    while (i < 10) {
        j = i;
        while (j > 0) {
            j = j+1;
        }
        i = i+1;
    }
    
    return 0;
}
