//#Unsafe
/*
 * Check that
 *  - pointer comparison with 0 is supported
 *  - local is not initialized with 0
 * Date: October 2013
 * Author: Christian Schilling, Matthias Heizmann
 * 
 * Pointer comparison with '0' is not supported.
 */

int main() {
    int* p;
    if (p != 0) {
        //@ assert \false;
    }
    return 0;
}
