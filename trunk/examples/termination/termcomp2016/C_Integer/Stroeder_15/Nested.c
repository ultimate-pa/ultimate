//#termcomp16-someonesaidyes
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
    int j;
    i = 0;
    j = 3;
    
    while (i < 10) {
        while (j < 12) {
            j = j-1;
            j = j+2;
        }
        i = i+1;
    }
    
    return 0;
}