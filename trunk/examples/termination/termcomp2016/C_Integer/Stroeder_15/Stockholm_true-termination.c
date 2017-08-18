//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
/*
 * Date: 2012-02-12
 * Author: leike@informatik.uni-freiburg.de
 *
 * Ranking function: f(x, a, b) = x;
 * needs the loop invariant b >= a.
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
    int x;
    int a;
    int b;
    x = __VERIFIER_nondet_int();
    a = __VERIFIER_nondet_int();
    b = __VERIFIER_nondet_int();
    if (a == b) {
        while (x >= 0) {
            x = x + a - b - 1;
        }
    }
    return 0;
}
