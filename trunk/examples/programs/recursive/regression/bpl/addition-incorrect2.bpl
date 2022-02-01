//#Unsafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: January 2012
 *
 * Recursive implementation of addition of natural numbers.
 * 
 * Program has several requres ensures and assert statements. Some do always
 * hold, some can be violated.
 */


procedure Main(a, b: int)  returns (c: int);
free requires a>=0;
free requires b>=0;
ensures c==a+b;

implementation Main(a, b: int) returns  (c: int)
{
  call c := addition(a,b);
  assert ((a==7 && b==7) ==> c==5);
}


procedure addition(x, y: int) returns (res: int);
requires x>=0;
requires y>=0;
ensures res >= x+y-2;

implementation addition(x, y: int) returns (res: int)
{
  if (y == 0) {
    res := x;
  }
  else {
    call res := addition(x+1, y-1);
  }
  assert (x+y >=0);
}
  
