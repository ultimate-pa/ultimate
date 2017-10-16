//#Safe
/*
 * Even tougher precision test for the join where one of the operands has a 
 * strong and the other weak equivalence over the same array pair.
 * 
 * compared to 44b this has a third branch which is supposed to expose the bug
 * even with a disjunctive rating of 2 (which currently is our default)
 * .. unfortunately this does not seem to work .. at least the bug is exposed in
 *  44b and 44c when disjunctive rating is 1.
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
  } else if (*) {
    assume a == b;
  } else if (*) {
    assume c[l] == 3;
    a := b[l := z];
  } else if (*) {
    assume a == b;
  } else {
    assume c[j] == 3;
    a := b[j := y];
  }
  assume c[k] != 3;
  assert a[k] == b[k];
}
