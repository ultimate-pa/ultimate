// Example depicted in Figure 3.2 of the following Bachelor Thesis.
// 2013 - Betim Musa - Trace Abstraction with Unsatisfiable Cores
//
// Author: musab@informatik.uni-freiburg.de and heizmann@informatik.uni-freiburg.de
// Date: 13.01.2014

var x, y : int;

procedure main() returns ();
modifies x,y;

implementation main() returns () {
  y := 0;
  x := y;
  while(x <= 0) {
    x := x + 1;
  }
  assert(y == 0);
}
