//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 19.3.2012
 * 
 * a in specification is b in implementation and vice versa
 */

var g: int;

procedure proc(b,a: int) returns (d,c: int);
requires b>=0;
ensures c == a+1;

implementation proc(a,b: int) returns (c,d: int)
{
  assert (a >=0);
  d := b+1;
}




  
