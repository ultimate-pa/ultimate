//#rNontermination
/*
 * Date: 04.01.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Integer hull of loop of Example 3.20. (we added two assumes)
 * Does not terminate over the reals.
 * Has linear ranking function f(x1,x2)=x1+x2-1 over the integers.
 * Loop is not integral.
 */

procedure main() returns () {
    var x1, x2: int;
    var x1old, x2old: int;
    while (-x1+x2 <= 0 && -x1-x2<=-1) {
        x1old = x1;
	x2old = x2;
        x2 := x2-2*x1+1;
	assume (-
    }
}

