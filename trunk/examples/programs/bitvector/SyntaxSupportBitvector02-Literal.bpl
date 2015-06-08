//#Unsafe
/* 
 * Author: heizmann@informatik.uni-freiburg.de, Thomas
 * Date: 2015-06-08
 */


var x:bv20;

procedure proc() returns ();

implementation proc() returns ()
{
  var y:bv20;
  y := 798bv20;
  assert x == y;
}

