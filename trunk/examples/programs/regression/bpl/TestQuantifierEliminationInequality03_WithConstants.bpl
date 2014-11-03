//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de, musab@informatik.uni-freiburg.de
 * Date: 2.11.2014
 * 
 */

var upper, lower, x, a,b,c: int;


procedure proc() returns ()
{
  assume upper >= x+2;
  assume x+2 >= lower;
  assume a <= upper;
  assume a >= lower;
  assume b <= upper;
  assume b >= lower;
  assume x+2 != a;
  assume x+2 != b;
  assume a != b;
  while (*) {
    //prevent large block encoding
  }
  assert upper >= lower + 2;
}




  
