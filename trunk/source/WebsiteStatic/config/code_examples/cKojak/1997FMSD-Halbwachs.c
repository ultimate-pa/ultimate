//#Safe
/*
 * Program depicted in Figure 7 of
 * 1997FMSD - Halbwachs,Proy,Roumanoff - Verification of Real-Time Systems using Linear Relation Analysis
 * 
 * Program was mentioned in 
 * 2009PLDI - Gulwani,Jain,Koskinen - Control-flow refinement and progress invariants for bound analysis
 * as "flagship example to motivate a new technique for proving non-trivial 
 * safety assertions"
 * 
 * Date: 25.6.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

int nondet() {
    int x;
    return x;
}

int main() {
    int t = 0, d = 0, s = 0;
    int sec, met;
    while (nondet()) {
        if (sec) {
            s = 0;
            if (t++ == 4) {
                break;
            }
        }
        if (met) {
            if (s++ == 3) {
                break;
            }
            d++;
            //@ assert (d != 10 );
        }
    }
}
