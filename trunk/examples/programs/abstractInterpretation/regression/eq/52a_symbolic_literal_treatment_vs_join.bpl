//#Safe
/*
 * Different literals always have different values.
 * Our implementation attempts to get around storing all the corresponding 
 * disequalites between literals by keeping them symbolic.
 * This test checks how we handle a difficulty with the symbolic treatment
 * and the join operation:
 *  If x equals 1, then implicitly x is different from all other literals.
 *  Now if we join such a stat with, say x equals 2, then there is no equality
 *  constraint about x we can keep, but all the disequalities from literals
 *  other than 1 or 2 still hold.
 *
 * This is the somewhat easier case for our analysis because the literal 3 is 
 * known to the analysis before the join.
 */
procedure main() {
  var x : int;
  x := 3;
  if (*) {
    x := 1;
  } else {
    x := 2;
  }
  assert x != 3;
}
