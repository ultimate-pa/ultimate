//#rTerminationDerivable
/*
 * Date: 2012-06-13
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * After RewriteArrays we have to apply RewriteBooleans
 *
 * f(x) = x is a ranking function together with the supporting invariant 
 * (if a[0] then 1 else 0) > 0
 * 
 */

var a: [int] bool;
var x: int;


procedure main() returns ()
modifies a, x;
{
    assume(a[0] == true);
    while (x >= 0) {
        if (a[0]) {
            x := x - 1;
        }
    }
}
