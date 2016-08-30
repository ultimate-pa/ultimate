typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
    i = __VERIFIER_nondet_int();
    
    while (i*i > 9) {
        if (i < 0) {
            i = i-1;
        } else {
            i = i+1;
        }
    }
	
    return 0;
}
