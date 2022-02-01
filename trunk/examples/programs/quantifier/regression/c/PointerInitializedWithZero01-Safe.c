//#Safe
/*
 * Check that
 *  - pointer comparison with 0 is supported
 *  - global pointer is initialized with 0
 * Date: October 2013
 * Author: Christian Schilling, Matthias Heizmann
 */

int* p;

int main() {
    if (p != 0) {
        //@ assert \false;
    }
    return 0;
}
