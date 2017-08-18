//#termcomp16-someonesaidyes
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
    int x;
    int y;
    i = __VERIFIER_nondet_int();
    x = 0;
    y = 0;
    
    if (i > 10) {
        x = 1;
    } else {
        y = 1;
    }
    while (x == y) { }
    
    return 0;
}
