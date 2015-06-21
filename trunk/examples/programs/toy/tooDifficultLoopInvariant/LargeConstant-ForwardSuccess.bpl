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
  var i,j: int;
  var a: [int]int;
  i := 0;
  while (*) {
	  assert i <= 1000;
	  assume i + 4 < a[j];
	  assume a[5] == 1000;
	  assume j > 4;
	  assume j < 6;
	  i := i + 4;
  }
}





  
