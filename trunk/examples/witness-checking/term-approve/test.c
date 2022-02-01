typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
    int c, x;
    x = __VERIFIER_nondet_int();
    c = __VERIFIER_nondet_int();
    if (c == 0) {
        while (x >= 0) {
            x = x + c;
        }
    }
    return 0;
}