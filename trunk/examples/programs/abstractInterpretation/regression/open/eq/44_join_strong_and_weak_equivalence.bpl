//#Safe
/*
 * I surmise that the join between a strong and a weak equivalence between two 
 * arrays is not treated correctly at the moment (5.10.2017).
 * This regression test should expose that.
 *
 * EDIT (14.10.2017): I don't think we can/want to prove this program with the 
 * eq domain, conceptually (for a disjunctive rating of 1). Because the either 
 * join would have to express something like "if j==i then a==b", or we would 
 * have to introduce a[j] magically.
 *
 * author: nutz@informatik.uni-freiburg.de
 */ 
procedure main() {
  var a, b : [int] int;
  var x, i, j : int;

  b[j] := 7;

  if (*) {
    assume a == b;
  } else {
    assume j != i;
    a := b[i := x];
  }
  assert a[j] == 7;
}
