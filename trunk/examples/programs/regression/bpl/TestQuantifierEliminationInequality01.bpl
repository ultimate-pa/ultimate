//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2.11.2014
 * 
 */

var a,b,x: int;


procedure proc() returns ()
{
  assume a > x;
  assume x > b;
  while (*) {
    //prevent large block encoding
  }
  assert a >= b + 2;
}




  
