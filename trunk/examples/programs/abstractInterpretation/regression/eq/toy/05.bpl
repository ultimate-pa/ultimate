//#Safe
procedure main() {
  var a1, b1 : [int] int;
  var a2, b2 : [int, int] int;
  var i, j, k : int;

  a1 := b1[i := k];

  // check that the weak equivalence holds
  assert a1 == b1[i := a1[i]];
  assert a1[i] == k;

   a2 := b2[i,j := k];

  // check that the weak equivalence holds
  assert a2 == b2[i, j := a2[i, j]];
  assert a2[i,j] == k;
}
