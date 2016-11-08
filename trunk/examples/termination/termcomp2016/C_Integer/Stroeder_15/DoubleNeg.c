typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
    int j;
    i = __VERIFIER_nondet_int();
    j = __VERIFIER_nondet_int();
    
    while (i*j > 0) {
        i = i - 1;
        j = j - 1;
    }
    
    return 0;
}
