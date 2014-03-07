//#Safe
// Bug in QE. a[i] replaced by 23, information i!=j ist lost.
//
// Author: heizmann@informatik.uni-freiburg.de
// Date: 18.10.2013

var a : [int] int;
var i,j,k : int;

implementation main() returns ()
{
  assume (a[i] == 23);
  assume (a[j] == 25);
  a[0] := a[i];
  assert (i != j && a[0] == 23);
}

procedure main() returns ();
  modifies a;

