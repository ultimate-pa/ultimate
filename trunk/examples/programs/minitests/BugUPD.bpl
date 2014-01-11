//#Safe
/*
 * Date: 02.11.2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 *
 */

var x,y,a,b : int;

procedure method1() returns ()
modifies x,y,a,b;
{
  assume((x != y && x == 0) || (a != b && a == 0));
  havoc y, b;
  assert(x == 0 || a == 0);
}


