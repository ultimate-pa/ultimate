//#Safe
/*
 * Currently we cannot prove correctness.
 * Loop invariant x % 65535 == y % 65535 would be sufficient for
 * correctness proof.
 * Alternative: introduce explicit case distinction for modulo operation.
 * 
 * Date: 2017-03-01
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main()
{
  var x, y: int;
  
  assume x == 0;
  assume y == 0;

  while (*) {
    x := x + 1;
    y := (y + 1) % 65535;
  }

  if (x == 31415) {
    assert (y == 31415);
  }
} 
