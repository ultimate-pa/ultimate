//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2.11.2014
 * 
 */

var x,lower,upper: real;


procedure proc() returns ()
{
  assume upper >= x;
  assume x >= lower;
  assume x != upper;
  while (*) {
    //prevent large block encoding
  }
  assert upper > lower;
}




  
