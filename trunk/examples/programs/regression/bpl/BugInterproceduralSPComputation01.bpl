//#Safe
/* 
Simple file, where our current computation of Call and  Return stmts fails.

Author: musab@informatik.uni-freiburg.de
*/


procedure proc() returns (res: int);

implementation proc() returns (res: int)
{
  res := 0;
  return;
}


procedure Main() returns ();

implementation Main() returns ()
{
  var z : int;
  call z := proc();
  assert(z == 0);
}




