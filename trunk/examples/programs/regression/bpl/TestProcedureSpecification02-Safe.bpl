//#Safe
/*
 * Reveals Bug in r11256. The argument g of the call is translated to the
 * term variable that represents g after the call.
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 11.03.2014
 *
 */

var g: int;

procedure caller();
modifies g;

implementation caller()
{
  var x: int;
  g:= 0;
  call x := callee(g);
  assert ( x == 1 );
}

procedure callee(b: int) returns (res: int);
modifies g;
ensures res == b+1;