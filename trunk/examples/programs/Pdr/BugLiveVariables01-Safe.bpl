//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 02.11.2013
 * 
 * Bug live variables. Is y live at the end of proc?
 *
 */

var x : int;
var y : int;


implementation main() returns ()
{
  x := y;
  call proc();
  assert false;
}

implementation proc() returns ()
{
  assume x != y;
}



procedure proc() returns ();
  modifies x;


procedure main() returns ();
  modifies x;


