//#termcomp16-someonesaidno
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int c;
    int i;
    c = (24*6)*6;
    
    if (c <= 10) {
        i = 0;
        while (i < 100) {
            i = i+1;
        }
    }
    else {
        if (c <= 50) {
            i = 0;
            while (i < 101) {
                i = i+1;
            }
        }
        if (c <= 100) {
            i = 0;
            while (i < 102) {
                i = i+1;
            }
        }
        else {
            i = 0;
            while (i < 103) {
                i = i+0;
            }
        }
    }
    
    return 0;
}
