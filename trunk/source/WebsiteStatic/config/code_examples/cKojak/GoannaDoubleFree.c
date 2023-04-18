//#Safe
/*
 * Example that occurs in the following papers which are related to the Goanna 
 * static analysis tool (http://redlizards.com/).
 * The program is correct (there is no double free) because free(p) is executed
 * only in the last iteration of the loop.
 * 
 * 2013ISSE - Ansgar Fehnker, Ralf Huuck - Model Checking Driven Static Analysis for the Real World
 * (Journal of Innovations in Systems and Software Engineering Springer-Verlag, doi:10.1007/s11334-012-0192-5, pages 1-12, August 2012.)
 * 2012ICFEM -  Maximilian Junker, Ralf Huuck, Ansgar Fehnker, Alexander Knapp -  SMT-Based False Positive Elimination in Static Program Analysis
 * 2012TAPAS -  Mark Bradley, Franck Cassez, Ansgar Fehnker, Thomas Given-Wilson, Ralf Huuck -  High Performance Static Analysis for Industry
 * 
 * A simplified version (without pointers) is used in our CAV paper.
 * 2013CAV - Heizmann,Hoenicke,Podelski - Software Model Checking for People Who Love Automata
 * 
 * Date: August 2012
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */
#include <stdlib.h>

int main() {
    int x, *a;
    int *p = malloc(sizeof(int));
    for (x = 10; x > 0; x--) {
        a = p;
        if (x == 1) {
            free(p);
        }
    }
    return 0;
}
