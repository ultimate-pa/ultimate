//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2.11.2014
 * 
 */

var upper, lower, x, a,b,c: int;


procedure proc() returns ()
{
  assume upper >= x;
  assume x >= lower;
  assume a <= upper;
  assume a >= lower;
  assume b <= upper;
  assume b >= lower;
  assume x != a;
  assume x != b;
  assume a != b;
  while (*) {
    //prevent large block encoding
  }
  assert upper >= lower + 2;
}




  
