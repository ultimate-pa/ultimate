//#Safe
/*
 * Program depicted in Figure 3 of
 * 2007POPL - Gulwani,Jojic - Program Verification as Probabilistic Inference
 * 
 * Program is cited in 
 * 2009PLDI - Gulwani,Jain,Koskinen - Control-flow refinement and progress invariants for bound analysis
 * as "flagship example to motivate a new technique for proving non-trivial 
 * safety assertions"
 * 
 * Date: 2013-06-27
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

int main(void) {
    int x = 0, y = 50;
     //@ loop invariant (x < 50 || x == y) && (x>=50 || y == 50) && x <= 100;
    while (x < 100) {
        if (x < 50) {
            x++;
        } else {
            x++;
            y++;
        }
    }
    //@ assert (y == 100);
}
