//#Safe
/*
 * Motivating example for hierarchical trace abstraction.
 * Maybe correct name is Brazil.
 * 
 * Date: 2016-11-22
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main()
{
  var x, y: int;
  var a: [int]int;

  
  assume (x > y);
  if (0 <= t && t <= 9997999) {
//     some float
  }
  //need modulo
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
