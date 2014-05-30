//#Safe
/*
 * Example that shows why totalinterpolant with superdifference may not 
 * terminate.
 * 
 * The program is correct. We never infer the loop invariant x == a || x == b
 * instead we unwind the loop once and annotate one node with x == a and the 
 * other with x == b.
 * 
 * If we build the total interpolation interpolant automaton we can never
 * add the selfloop at the unwinding node(s).
 * If we now use the superdifference (without adding additional edges) we are
 * not able to "exclude" this selfloops.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 29.5.2014
 */


procedure proc();

implementation proc()
{
  var x,y,a,b: int;
  x := a;
  y := b;
  while (*) {
    x,y := y,x;
  }
  assert x == a || x == b;
}





  
