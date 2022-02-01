//#Safe
/*
 * revealed bug in revision <=r5522
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 06.04.2012
 * 
 * 
 */

procedure proc();

implementation proc()
{
  var a: int;
  var b: int;
  
  a := 0;
  b := 7;
  a, b := b+1, a+2;
  assert ( a == 8 && b == 2 );
}





  
