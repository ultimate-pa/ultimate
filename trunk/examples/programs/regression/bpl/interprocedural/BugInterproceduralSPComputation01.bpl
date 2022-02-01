//#Safe
/* 
Simple file, where our current computation of Call and  Return stmts fails.

Author: musab@informatik.uni-freiburg.de
*/


procedure p2(x: int) returns (res: int);

implementation p2(x : int) returns (res: int)
{
  res := x;
  return;
}


procedure Main() returns ();

implementation Main() returns ()
{
  var z : int;
  var y : int;
  y := 0;
  call z := p2(y);
  assert(z >= 0);
}




