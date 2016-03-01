//#Unsafe
/* 
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-02-18
 */

type { :builtin "FloatingPoint" } { :indices 5, 11 } myFloat;

function{:builtin "fp.eq"} FP_EQ(x:myFloat, y:myFloat) returns (bool);

procedure proc() returns ();

implementation proc() returns ()
{
  var x,y:myFloat;
  y := x;
  assert FP_EQ(x,y);
}

