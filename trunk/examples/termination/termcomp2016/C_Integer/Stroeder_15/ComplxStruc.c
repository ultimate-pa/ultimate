//#termcomp16-someonesaidno
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
    int j;
    i = __VERIFIER_nondet_int();
    j = i;
    
    while (i > 0) {
        if (i >= j) {
            i = i+1;
            if (j < 5) {
                j = j+1;
                if (i-j>2) {
                    i = i+1;
                } else {
                    j = j+1;
                }
            } else {
                j = j-1;
            }
        } else {
            if (i > 0 && j < 0) {
                i = i-1;
                if (j < -1) {
                    j = j+1;
                } else {
                    i = i+1;
                }
            } else {
                i = i+1;
                if (j*2 > i) {
                    j = j-1;
                } else {
                    j = j+1;
                }
            }
        }
        
    }

    return 0;
}
