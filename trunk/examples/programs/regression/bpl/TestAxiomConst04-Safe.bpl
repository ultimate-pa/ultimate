//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-03-25
 * 
 */

const c : int;
axiom c == 23;

procedure proc() returns ()
modifies;
{
  var x : int;
  x := c;
  assert(x == 23);
}



  
