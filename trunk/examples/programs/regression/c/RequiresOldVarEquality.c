//#Safe
/*
 * To prove this program correct, Ultimate needs to consider the implicit precondition that g == old(g).
 * As of 2024-12-18, this precondition was not considered in library mode, and thus Automizer wrongly claimed that this program is incorrect.
 */

extern void reach_error(void);
extern char __VERIFIER_nondet_char();

int g;

//@ requires g < 1048;
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
