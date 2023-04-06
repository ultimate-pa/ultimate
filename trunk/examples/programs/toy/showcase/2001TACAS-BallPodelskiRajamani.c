//#Safe
/*
 * Example from 
 * 2001TACAS - Ball,Podelski,Rajamani - Boolean and Cartesian Abstraction for 
 * Model Checking C Programs.
 * http://link.springer.com/chapter/10.1007%2F3-540-45319-9_19
 */

extern short __VERIFIER_nondet_short(void);

int main() {
    int x, y, z, w;
    y = __VERIFIER_nondet_short();
    w = __VERIFIER_nondet_short();
    do {
        z = 0;
        x = y;
        if (w) {
            x++;
            z=1;
        }
    } while (x!=y);
    if (z) {
        //@ assert \false;
    }
}
