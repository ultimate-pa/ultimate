//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 08.03.2014
 * 
 */

function sum(summand1:int, summand2:int) returns (int)
{
  summand1 + summand2
}

var a,b:int;

procedure proc() returns ()
modifies a,b;
{
  assume(sum(a,b) == a+b+1);
  assert(false);
}


