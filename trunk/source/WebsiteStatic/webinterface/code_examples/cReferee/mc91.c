extern void reach_error(void);
extern char __VERIFIER_nondet_char();

//@ ensures (x >= 101 || \result == 91) && (x <= 100 || \result == x - 10);
int mc(int x) {
    if (x>100) {
        return x - 10;
    } else {
        return mc(mc(x + 11));
    }
}

void myFunction(char x) {
    int y = mc(x);
    if (x < 100 && y != 91) {
        reach_error();
    }
}
