//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 10.11.2011
 * 
 * Revealed bug in revision r4390. 
 * If a global g is modified on a call, g is not in modified in the called
 * procedure it was not correctly renamed.
 *
 */

var g: int;

procedure Main(z: int);
modifies g;

implementation Main(z: int)
{
  var b,c: int;
  g := 0;
  b := 1;
  call g := bar(b);
  assert (g == 0 || g == 1);
}


procedure bar(y: int) returns (res: int);

implementation bar(y: int) returns (res: int)
{
  if (*) {
    res := g;
    return;
  }
  else {
    assume true;
    if (*) {
      assume true;
    }
    else {
      assume true;
    }
    res := g + y;
    return;
  }
}