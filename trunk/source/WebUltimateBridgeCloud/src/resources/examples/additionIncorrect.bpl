//UNSAFE;NOPRELUDE
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: August 2010
 *
 * Recursive implementation of addition of natural numbers.
 * 
 * The assert statement at the end of the Main procedure violates correctness
 * of this program. But about 12 iterations are necessary to show this.
 */


procedure Main(a, b: int);
free requires a>=0;
free requires b>=0;
ensures c==a+b;

implementation Main(a, b: int)
{
  var c: int;
  call c := addition(a,b);
  assert ((a==7 && b==7) ==> c==5);
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
  
