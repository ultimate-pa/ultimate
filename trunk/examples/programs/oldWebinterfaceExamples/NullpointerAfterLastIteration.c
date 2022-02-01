//#mSafe
/*
 * Pointer free abstraction of example that Andreas discussed during his stay
 * at NICTA in Australia.
 * 
 * Date: November 2012
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

int main() {
    int x, n;
    x = 1;
    while ( n>=0 ) {
        //@ assert x != 0;
        if (n == 0) {
            x = 0;
        }
        n--;
    }
    return 0;
}