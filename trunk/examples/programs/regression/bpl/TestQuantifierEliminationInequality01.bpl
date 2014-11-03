//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2.11.2014
 * 
 */

var a,b,c: int;


procedure proc() returns ()
{
  assume a > b;
  assume b > c;
  while (*) {
    //prevent large block encoding
  }
  assert a >= c + 2;
}




  
