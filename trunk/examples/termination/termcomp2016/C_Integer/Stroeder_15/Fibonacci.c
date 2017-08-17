//#termcomp16-someonesaidno
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int n;
    int i;
    int j;
    int t;
    n = __VERIFIER_nondet_int();
    i = 0;
    j = 1;
    t = 0;
    
    while (j != n) {
        t = j+i;
        i = j;
        j = t;
    }
	
    return 0;
}
