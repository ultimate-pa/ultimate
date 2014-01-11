//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 10.11.2011
 * 
 * Revealed bug in revision 4393. 
 * Computed Hoare annotation is not inductive if abstractions are minimized.
 *
 */

var g, f: int;

procedure Main(z: int);
modifies g, f;

implementation Main(z: int)
{
  var b,c: int;
  g := 0;
  f := 1;
  call g := bar(f);
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
    res := g + f;
    return;
  }
}