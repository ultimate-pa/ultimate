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

extern int __VERIFIER_nondet_int(void);

int main() {
    int t = 0, d = 0, s = 0;
    int sec = __VERIFIER_nondet_int();
    int met = __VERIFIER_nondet_int();
    while (__VERIFIER_nondet_int()) {
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
