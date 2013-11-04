/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * Pointer p1 is both addressoffed and
 * dereferenced which breaks an assertion.
 */
int main() {
    int* p1;
    int** p2 = &p1;
    *p1 == 0;

    return 0;
}
