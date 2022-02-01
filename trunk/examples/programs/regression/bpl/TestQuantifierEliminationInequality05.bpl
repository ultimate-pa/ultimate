//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-07-23
 * 
 */

var a,b,c: real;


procedure main() returns ()
modifies b;
{
  assume (a + 2.0 * b <= c) && 0.0 < b;
  havoc b;
  while (*) {
    //prevent large block encoding
  }
  assert a < c;
}




  
