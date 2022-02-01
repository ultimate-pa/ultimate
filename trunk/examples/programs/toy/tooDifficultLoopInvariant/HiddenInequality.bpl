//#Safe
/*
 * Loop invariant s >= i is sufficient.
 * 
 * Before today, the invariant synthesis with unsat core and WP constraints
 * was unable to find an annotation.
 * Reason: WP at the loop head is i<=8 || s>=9. 
 * WP is later negated over the reals and constraints become infeasible.
 * 
 * Our solution/workaround. Negate WP directly over the ints.
 * 
 * Date: 2017-03-18
 * Author: heizmann@informatik.uni-freiburg.de and Betim Musa
 *
 */


var i : int;
var s : int;


implementation ULTIMATE.start() returns (){
    s := 0;
    i := 0;
    while (i <= 8) {
    s := s + 1;
    i := i + 1;
    }
    assert (s >= 9);
}

procedure ULTIMATE.start() returns ();
modifies s,i;


