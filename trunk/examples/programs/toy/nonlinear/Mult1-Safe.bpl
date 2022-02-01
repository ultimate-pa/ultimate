//#Safe
/*
 * Date: 2015-01-24
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */


procedure mult(a,b: int) returns (res: int)
requires b >=0;
ensures res == a * b;
{
  var tmp: int;

  res := 0;
  tmp := b;

  while (tmp > 0)
  {
    res := res + a;
    tmp := tmp - 1;
  }
  
}
