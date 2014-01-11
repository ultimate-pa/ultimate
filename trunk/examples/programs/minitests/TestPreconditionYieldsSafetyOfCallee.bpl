//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 20.3.2012
 * 
 */

var g: int;

procedure proc(b,a: int) returns (d,c: int);
requires g==0;


implementation proc(a,b: int) returns (c,d: int)
{
  assert (g >=0);
}




  
