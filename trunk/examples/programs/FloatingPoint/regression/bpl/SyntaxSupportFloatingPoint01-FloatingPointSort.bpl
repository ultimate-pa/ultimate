//#Safe
/* 
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-12-14
 */

type { :builtin "FloatingPoint" } { :indices 5, 11 } theBoogieFloatType;


procedure proc() returns ();

implementation proc() returns ()
{
  var x,y:theBoogieFloatType;
  y := x;
  // The equality == here has a different semantics than bitvector comparison
  // in C. Bitvector comparison in C will be translated to fp.eq which is not 
  // reflexive e.g., if the operand is a NaN
  assert x == y;
}

