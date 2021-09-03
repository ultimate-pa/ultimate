//#Safe
/*
 * Author: Matthias Heizmann
 * Date: 2021-04-22
 * 
 */

procedure main() returns () {
  var a : [int] int;
  var i,k, N, sum : int;
  i := 0;
  sum := 0;
  a[k] := 3;
  while(i <= N)
  {
      sum := sum + a[k];
      i := i + 1;
  }
  assert sum >= 2 * N;
}


