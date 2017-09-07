//#termcomp16-someonesaidno
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int bob;
    int samantha;
    int temp;
    bob = 13;
    samantha = 17;
    
    while (bob + samantha < 100) {
        temp = bob;
        bob = samantha;
        samantha = temp;
    }
    
    return 0;
}