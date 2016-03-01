//#Safe
/* 
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-03-01
 */

type {:builtin "FloatingPoint"} {:indices 5, 11} myFloat;

function{:builtin "fp"} FP(sb1:bv1, eb:bv5, sbTail:bv10) returns (myFloat);

// we can use a 0-ary function to represent the +oo literal
function{:builtin "+oo"} {:indices 5, 11} PLUS_INFINITY_16() returns (myFloat);

// alternatively, we can use a constant to define the +oo literal
// I prefer this alternative.
const{:builtin "+oo"} {:indices 5, 11} plus_infinity_16: myFloat;

procedure proc() returns ();

implementation proc() returns ()
{
  var x,y:myFloat;
  x := FP(0bv1, 31bv5, 0bv10);
  y := PLUS_INFINITY_16();
  assert x == y;
  assert PLUS_INFINITY_16() == plus_infinity_16;
}

