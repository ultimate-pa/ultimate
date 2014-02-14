//#Safe
/*
 * Date: 29.02.2012
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Reveals bug in Modifies Checker. Only the local x but not the global x is
 * modified
 */

var x: int;

procedure ModifiesBug()
{
  var x: bool;

  x := true;
  assert(x != false);
}

