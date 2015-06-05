//#Safe
/* 
 * One of the simplest programs with bitvectors that I can imagine.
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 3.6.2015
 */


var x:bv20;

procedure proc() returns ();

implementation proc() returns ()
{
  var y:bv20;
  y := x;
  assert x == y;
}

