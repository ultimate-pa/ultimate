//#Safe
/*
 * Even tougher precision test for the join where one of the operands has a 
 * strong and the other weak equivalence over the same array pair.
 * 
 * attempt of a minimized version of 44c
 *
 * author: nutz@informatik.uni-freiburg.de
 */ 
procedure main() {
  var a, b, c : [int] int;
  var x, y, z, i, j, k, l : int;

  if (*) {
    assume a == b;
  } else if (*) {
    assume c[i] == 3;
    a := b[i := x];
  } else {
    assume c[j] == 3;
    a := b[j := y];
  }
  assume c[k] != 3;
  assert a[k] == b[k];
}
