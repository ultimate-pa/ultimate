/*
 * Date: 2015-07-06
 * Author: Thomas Stroeder (stroeder@informatik.rwth-aachen.de)
 *
 * This is the Collatz function in the C Integer Programs format.
 * Comment: termination status unknown
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x, y;
    x = __VERIFIER_nondet_int();
    while (x > 1) {
        // inlined mod 2
        y = x;
        while (y > 1) {
            y = y - 2;
        }
        if (y == 0) {
            // inlined div 2
            while (2*y < x) {
                y = y + 1;
            }
            x = y;
        } else {
            x = 3*x + 1;
        }
    }
    return 0;
}
