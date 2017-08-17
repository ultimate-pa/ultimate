//#termcomp16-someonesaidno
typedef enum {false,true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x;
    int y;
    int z;
    int res;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    z = y;
    res = 0;
    
    while (z > 0 && (y == 0 || y > 0 && x > 0))	{
        
        if (y == 0) {
            res = res + 1;
            y = z;
        }
        else {
            x = x + 1;
            y = y - 1;
        }
    }
    
    return 0;
}

