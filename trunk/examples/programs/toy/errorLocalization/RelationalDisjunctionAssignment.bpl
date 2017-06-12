//#Unsafe
/* Example that we discussed on Monday 12th May in the context of a new
 * definition of relevancy/resposibility.
 * 
 * According to our algorithm both assignments are responsible for the
 * error.
 * 
 * The argument of the assume x!=y can be also seen as a disjunction
 * (x<y || y<x). In contrast to the UnrelationalDisjunction.bpl example
 * bot disjuncts are related.
 * 
 * Author: Christian Schilling, Matthias Heizmann, Numair Mansur
 * Date: 2017-06-12
 * 
 * 
 */

procedure main() returns () {
  var x, y : int;
  x := 1;
  y := 2;
  assume(x != y);
  assert(false);
}


