//#rTerminationDerivable
/*
 * Date: 2015-05-01
 * Author: heizmann@informatik.uni-freiburg.de
 * Reveals bug in 14213 in RewriteArrays
 * We obtain the following which is incorrect because of a possible alias 
 * between i and k. Only reproduceable if we do not simplify termination 
 * arguments.
 * Ranking function f((select a i), tmp2, tmp, x) = -2*(select a i) + 3*tmp2 - 1*tmp + 8*x
 * Supporting invariants [-2*(select a i) + 3*tmp2 - 1*tmp + 4 >= 0]
 *
 */

var a : [int]int;
var k : int;
var some : int;
var i : int;
var tmp : int;
var tmp2 : int;
var x : int;

procedure main() returns ()
modifies a, x, tmp, tmp2;
{
  tmp := a[i];
  tmp2 := tmp;
  while (x > 0) {
    a[k] := some;
    x := x - 1;
  }
}




