//#Safe
/*
 * Variation of the Luxembourg example with arrays.
 * The loop invariant (x > y && 1000-a[y]>=a[x]) allows us to prove correctness.
 * 
 * Date: 2016-04-15
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main()
{
  var x, y: int;
  var a: [int]int;
  
  assume (x > y);
  
  a[x] := 0;
  a[y] := 1000;

  while (*) {
    a[x] := a[x] + 1;
    a[y] := a[y] - 1;
  }
  
  if (a[x] == 1000) {
    assert (a[y] <= 0);
  }

} 
