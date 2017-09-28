//#Safe
/*
 * Test that checks for the definition of  weak equivalence, expressed as an 
 * equality with a store.
 * Currently we cannot verify this because we overapproximate the negation of 
 * an array equality where one element is a store by "true".
 */
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
