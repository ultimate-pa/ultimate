//#termcomp16-someonesaidyes
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
    int j;
    int k;
    int t;
    i = __VERIFIER_nondet_int();
    j = __VERIFIER_nondet_int();
    k = __VERIFIER_nondet_int();
    
    while (i <= 100 && j <= k) {
        i = j;
        j = i + 1;
        k = k - 1;
    }
    
    return 0;
}
