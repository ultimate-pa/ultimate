//#termcomp16-someonesaidno
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int n;
    int sum;
    n = __VERIFIER_nondet_int();
    sum = 0;
    
    while (n != 0) {
        sum = sum + n;
        n = n - 1;
    }

    return 0;
}
