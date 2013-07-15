/*
 Author: musab@informatik.uni-freiburg.de
 This program is an example from by bachelor thesis.
 Program is correct with respect to the specification.
 ULTIMATE can prove its correctness.
 It needs 11 iterations, and it takes ~10 seconds to prove it.
*/

procedure Main(z : int) returns ();
requires z >= 0;

implementation Main(z : int) returns () {
  var x, y : int;
  x := 0;
  y := x;
  while(x < z) {
    x := x + 1;
  }
  assert(y == 0);
  assert(x >= 0);
}


