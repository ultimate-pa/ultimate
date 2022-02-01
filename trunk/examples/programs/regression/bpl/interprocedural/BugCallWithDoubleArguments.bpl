//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 14.5.2012
 *
 */


procedure caller(a: int);

implementation caller(a: int)
{
  var b, c: int;
  call b := callee(a,a);
  assert ( b == 1);
}



procedure callee(m,n: int) returns (res: int);

implementation callee(m,n : int) returns (res: int)
{
   res := 1;
}


