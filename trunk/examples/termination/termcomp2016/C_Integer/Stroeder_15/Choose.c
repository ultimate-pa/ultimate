//#termcomp16-someonesaidno
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
    i = 3;

    while (i >= 3) {
        if (i > 5) {
            i = i+3;
        } else {
            if (i > 10) {
                i = i-2;
            } else {
                i = i+1;
            }
        }
    }

    return 0;
}
