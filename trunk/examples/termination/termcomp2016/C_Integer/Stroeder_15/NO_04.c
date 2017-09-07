//#termcomp16-someonesaidno
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
    int j;
    int k;
    int l;
    int m;
    int a;
    int b;
    i = 0;
    
    while (i < 100) {
        a = i+2;
        j = 0;
        while (j < a) {
            k = i+j+3;
            while (k >= 0) {
                b = i+j+k+4;
                l = 0;
                while (l < b) {
                    m = i+j+k+l+1000;
                    while (m >= 0) {
                        m = m-0;
                    }
                    l = l+1;
                }
                k = k-1;
            }
            j = j+1;
        }
        i = i+1;
    }
    
    return 0;
}
