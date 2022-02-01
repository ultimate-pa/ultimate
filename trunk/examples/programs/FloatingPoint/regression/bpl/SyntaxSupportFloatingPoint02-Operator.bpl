//#Unsafe
/* 
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-02-18
 */

type { :builtin "FloatingPoint" } { :indices 5, 11 } myFloat;

function{:builtin "fp.eq"} FP_EQ(x:myFloat, y:myFloat) returns (bool);

// we can use a 0-ary function to represent the NaN literal
// we need this for the backtranslation in case the SMT solver returns
// the NaN literal
function{:builtin "NaN"} {:indices 5, 11} NaN_16() returns (myFloat);

procedure proc() returns ();

implementation proc() returns ()
{
  var x,y:myFloat;
  y := x;
  assert FP_EQ(x,y);
}

