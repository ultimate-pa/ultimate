//#Safe
/*
 * Minor modification of "BugHoareAnnotationWithMinimiation.bpl". 
 * In this example the variable 'g' is in bar's set of modifiable variables.
 * 
 * Revealed bug in the MonolithicHoareTripleChecker for the special case
 * where a modifiable global variable is assigned at the return of the called
 * procedure.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-12-25
 * 
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
modifies g;

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
