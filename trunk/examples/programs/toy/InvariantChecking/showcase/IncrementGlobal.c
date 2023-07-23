extern void reach_error(void);
extern char __VERIFIER_nondet_char();

int g;

//@ ensures (g > \old(g));
void increment() {
    g++;
     //@ loop invariant g > \old(g);
    while(__VERIFIER_nondet_char()) {
        if (g < 2147483647) {
            g++;
        }
    }
}

void myFunction(char x) {
    g = x;
    increment();
    if (x >= g) {
        reach_error();
    }
}
