//#Safe
/*
 * regression test for one aspect of backward congruence:
 * if we add an equality x = y
 * and x = a[i], and y != a[j]
 * or respectively x = a[i] and y != b[i]
 * we can propagate i != j, or a != b respectively
 */
procedure main() {
  var x, y, i, j : int;
  var a, b : [int] int;

  assume x == a[i];
  assume y != b[j];
  assume a == b;

  assume x == y;

  assert i != j;

  havoc a, b, x, y, i, j;
  
  assume x == a[i];
  assume y != b[j];
  assume i == j;

  assume x == y;

  assert a != b;
}
 
