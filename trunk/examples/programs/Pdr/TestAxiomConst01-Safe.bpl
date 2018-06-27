//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 08.03.2014
 * 
 */

const c : int;
axiom c == 23;

procedure proc() returns ()
modifies;
{
  assert(c == 23);
}



  
