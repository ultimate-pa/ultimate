//#Safe
/*
 * Pointer free abstraction of example that Andreas discussed during his stay
 * at NICTA in Australia.
 * 
 * Original version of the program as it occurs in
 * Ansgar Fehnker, Ralf Huuck
 * Model Checking Driven Static Analysis for the Real World
 * Journal of Innovations in Systems and Software Engineering Springer-Verlag, doi:10.1007/s11334-012-0192-5, pages 1-12, August 2012. 
 * 
 * Date: August 2012
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */
#include <stdlib.h>

int main() {
    int x, *a;
    int *p = malloc(sizeof(int));
    x = 10;
    while ( x > 0 ) {
        a = p;
        if (x == 1) {
            free(p);
        }
        x--;
    }
    return 0;
}
