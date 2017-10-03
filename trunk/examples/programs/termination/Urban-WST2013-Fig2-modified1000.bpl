//#Terminating
/*
 * Program from Fig.1 of
 * 2013WST - Urban - Piecewise-Defined Ranking Functions
 * 
 * 
 * The program is terminating because x1 is increased and bound from above by 10.
 * However, every counterexample that we get also takes the inner loop.
 * 
 * Now, there are two reasons for the infeasibility of the counterexample. The 
 * reason mentioned above that argues about x1. The second reason is that we 
 * cannot leave the inner loop before taking it 1000 times.
 * 
 * The second reason is simpler, Ultimate always only infers the second reason. 
 * However the second reason cannot be generalized to a termination proof for the 
 * program.
 *
 * Date: 2017-10-03
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

var x1,x2: int;

procedure main()
modifies x1,x2;
{
    while (x1 <= 10) {
        x2 := 1000;
        while (x2 > 1) {
            x2 := x2 -1;
        }
        x1 := x1 + 1;
    }

}
