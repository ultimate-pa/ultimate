//#Unsafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 08.03.2014
 * 
 */

function inc(int) returns (int);
axiom (forall i:int :: inc(i) == i+1);

procedure proc() returns ()
modifies;
{
  assert(inc(2) == 42);
}



  
