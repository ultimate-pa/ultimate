//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: August 2012
 *
 */

var g: int;
var m: int;

procedure Main();
modifies m;

implementation Main()
{
  call assignProc();
  assert g == m;
}

procedure assignProc() returns ();
modifies m;

implementation assignProc() returns ()
{
  m := g;
}
  
