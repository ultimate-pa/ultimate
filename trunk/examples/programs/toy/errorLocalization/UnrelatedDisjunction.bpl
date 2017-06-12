//#Unsafe
/*
 * According to our algorithm non of the assignments is responsible 
 * for the error.
 * 
 * In contrast to the RelationalDisjunctionAssignment.bpl example
 * bot disjuncts are not related.
 * 
 * 
 * Author: Christian Schilling, Matthias Heizmann, Numair Mansur
 * Date: 2017-06-12
 * 
 * 
 */

procedure main() returns () {
  var x, y : int;
  x := 5;
  y := 7;
  assume(x == 5 || y == 7);
  assert(false);
}


