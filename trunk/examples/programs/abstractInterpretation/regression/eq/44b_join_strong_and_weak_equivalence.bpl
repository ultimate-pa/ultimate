//#Safe
/*
 * Even tougher precision test for the join where one of the operands has a 
 * strong and the other weak equivalence over the same array pair.
 * 
 *
 * author: nutz@informatik.uni-freiburg.de
 */ 
procedure main() {
  var a, b, c : [int] int;
  var x, i, j : int;

  if (*) {
    assume a == b;
  } else {
    assume c[i] == 3;
    a := b[i := x];
  }
  assume c[j] != 3;
  assert a[j] == b[j];
}
