//#Unsafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 5.6.2012
 * 
 * 
 */

procedure proc();

implementation proc()
{
  var x:int;
  
  x := 0;
  if (*) {
    x := -1;
  }
  assert ( x == 0 );
}




  
