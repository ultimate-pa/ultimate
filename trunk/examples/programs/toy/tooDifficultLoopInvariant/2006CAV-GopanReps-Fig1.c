//#Safe
/*
 * Program depicted in Figure 1 of
 * 2006CAV - Gopan,Reps - Lookahead Widening
 * 
 * Program is mentioned in 
 * 2009PLDI - Gulwani,Jain,Koskinen - Control-flow refinement and progress invariants for bound analysis
 * as "flagship example to motivate a new technique for proving non-trivial 
 * safety assertions"
 * 
 * Date: 2013-06-27
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

int main(void) {
    int x = 0, y = 0;
    while (1) {
        if (x <= 50) {
            y++;
        } else {
            y--;
        }
        if (y<0) {
            break;
        }
        x++;
    }
    //@ assert (x == 102);
}
