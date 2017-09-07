//#termcomp16-someonesaidyes
/*
 * Program from the introduction of
 * 2013CAV - Brockschmidt,Cook,Fuhs - Better termination proving through cooperation -draft
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x, y;
    x = __VERIFIER_nondet_int();
    y = 1;
    while (x > 0) {
        x = x - y;
        y = y + 1;
    }
    return 0;
}
