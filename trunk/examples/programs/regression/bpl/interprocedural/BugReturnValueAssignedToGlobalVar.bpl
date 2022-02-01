//#Safe
/*
 * Bug in r7069. Local BoogieVar for left hand side of call was created instead
 * of using the global variable.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 29.9.2012
 *
 */

var g: int;

procedure caller(a: int);
modifies g;

implementation caller(a: int)
{
  call g := callee();
  assert ( g == 1);
}



procedure callee() returns (res: int);

implementation callee() returns (res: int)
{
   res := 1;
}


