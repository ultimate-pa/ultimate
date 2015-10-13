//#Termination
/*
 * Date: November 2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * 
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int y = __VERIFIER_nondet_int();
	int z = __VERIFIER_nondet_int();
    int x;
    if (__VERIFIER_nondet_int()) {
        x = 1;
    } else {
        x = -1;
    }
    if (x > 0) {
        x++;
    } else {
        x--;
    }
    if (x > 0) {
        x++;
    } else {
        x--;
    }
    if (x > 0) {
        x++;
    } else {
        x--;
    }
    if (x > 0) {
        x++;
    } else {
        x--;
    }
    if (x > 0) {
        x++;
    } else {
        x--;
    }
    if (x > 0) {
        x++;
    } else {
        x--;
    }
    if (x > 0) {
        x++;
    } else {
        x--;
    }
    if (x > 0) {
        x++;
    } else {
        x--;
    }
    while (y<100 && z<100) {
        y = y+x;
        z = z-x;
    }
    return 0;
}
