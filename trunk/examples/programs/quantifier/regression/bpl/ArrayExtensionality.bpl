//#Safe
// Example where iZ3 returns an interpolant that contains the
//     array-ext
// symbol.
//
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-03-21


procedure noMemleak() returns () {
  var a,b : [int]bool;
  b := a;
  assume (a[7] == false);
  while(*) { }
  a[7] := true;
  a[7] := false;
  assert(a == b);
}