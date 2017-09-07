//#termcomp16-someonesaidno
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
    int j;
    i = __VERIFIER_nondet_int();
    j = __VERIFIER_nondet_int();
    
    while (true) {
        if (i < j) {
            i = i+4;
        } else {
            j = j+1;
            i = i+2;
        }
    }
	
    return 0;
}
