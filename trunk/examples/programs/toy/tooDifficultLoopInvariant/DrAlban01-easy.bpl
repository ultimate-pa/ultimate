//#Safe
/*
 * One would expect that the predicate after the loop is a loop
 * invariant if we use our computation of interpolants that is 
 * based on strongest post (especially if we use loop acceleration).
 * 
 * However, if we use the setting in which we project predicates
 * to the variables that are live at this position in the trace
 * we quantify the variable y, loose the information that
 * y is positive (resp. y is four), and the predicate after the
 * loop cannot be a loop invariant.
 * 
 * Variant of this example where we check only that x is non-negative.
 * 
 * Date: 2022-06-18
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main()
{
  var x, y, z: int;
  
  x := 0;
  y := 4;

  while (*) {
    x := x + y;
  }
  
  assert (//x != z*2+1 && 
  x >= 0);


} 
