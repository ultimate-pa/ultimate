//#Safe
/*
 * Example where modifiable global variable is argument of procedure call.
 * Author: Betim Musa and heizmann@informatik.uni-freiburg.de
 * Date: 05.08.2013
 * 
 */

var g: int;

procedure Main();
modifies g;

implementation Main()
{
  var a: int;
  g := a;
  call a := bar(g);
  assert (a == g - 2);
}


procedure bar(y: int) returns (res: int);
modifies g;

implementation bar(y: int) returns (res: int)
{
  res := y + 1;
  g := g + 3;
}