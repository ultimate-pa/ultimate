//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: August 2010
 *
 * Recursive implementation of addition of natural numbers.
 * 
 * The program is correct with respect to the ensures clause of the Main
 * procedure.
 */


procedure Main(a, b: int) returns (c: int);
free requires a>=0;
free requires b>=0;
ensures c==a+b;

implementation Main(a, b: int) returns (c: int)
{
  call c := addition(a,b);
//  assert ((a==5 && b==7) ==> c==5);
}


procedure addition(x, y: int) returns (res: int);
requires x>=0;
requires y>=0;

implementation addition(x, y: int) returns (res: int)
{
  if (y == 0) {
    res := x;
    res := res *1;
  }
  else {
    call res := addition(x+1, y-1);
  }
}
  
