//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 20.3.2012
 * 
 */

var g: int;

procedure caller(a: int);

implementation caller(a: int)
{
  var b: int;
  call b := callee(a);
  assert ( a+b>=0 );
}

procedure callee(c: int) returns (d: int);
ensures c+d>=0;




  
