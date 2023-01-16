//#Safe
/*
 * Author: Matthias Heizmann
 * Date: 2021-04-22
 * 
 */
var i, N, sum : int;
procedure main() returns () 
modifies i,N,sum;
{
  assume N >= 0;
  i := 1;
  sum := 0;
  while(i < N)
  {
      sum := sum + i;
      i := i + 1;
  }
  assert sum == N*(N-1)/2;
}


