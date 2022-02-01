//#Safe
/*
 * Date: 2015-01-14
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */


procedure power(a,b: int) returns (res: int)
requires a >=1 && b >=0;
ensures res >= 0;
{
  var tmp: int;

  res := 1;
  tmp := b;

  while (tmp > 0)
  {
    res := res * a;
    tmp := tmp - 1;
  }
  
}
