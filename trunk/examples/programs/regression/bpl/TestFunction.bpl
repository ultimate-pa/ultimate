//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 24.5.2012
 */


function myFunc(in: int) returns (res : bool);
//axiom(myFunc(7)==true);


procedure proc();

implementation proc()
{
  var x: int;
  assume (myFunc(7)==true);
  x := 7;
  assert (myFunc(x)==true);
}





  
