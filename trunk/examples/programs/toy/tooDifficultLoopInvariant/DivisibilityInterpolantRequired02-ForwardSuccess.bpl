//#Safe
/*
 * Modified version of DivisibilityInterpolantRequired01.bpl example where
 * we succeed with ForwardPredicate but we fail with BackwardPredicates.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2014-08-01
 */

procedure proc();

implementation proc()
{
  var a: int;
  assume a % 2 == 0;
  while (*) {
	  a := a + 2;
  }
  assert a != 7;
}





  
