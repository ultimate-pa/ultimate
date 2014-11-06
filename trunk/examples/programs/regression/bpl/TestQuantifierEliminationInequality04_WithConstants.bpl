//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de, musab@informatik.uni-freiburg.de
 * Date: 2.11.2014
 * 
 */

var x,a,b,c,d: real;


procedure proc() returns ()
{
  assume a >= x;
  assume x >= b;
  assume x != a;
  assume x >= 1.0;
  while (*) {
    //prevent large block encoding
  }
  assert a > b;
}




  
