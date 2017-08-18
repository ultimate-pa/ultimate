//#termcomp16-someonesaidno
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
    int j;
    j = 0;
    i = 0;
    
    while (i <= j) {
        if (j-i < 1) { j = j+2; }
        i = i+1;
    }
    
    return 0;
}
