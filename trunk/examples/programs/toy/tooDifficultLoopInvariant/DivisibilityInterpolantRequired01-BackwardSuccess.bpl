//#Safe
/*
 * Example where we fail with tree interpolation because we never obtain
 * interpolants like a % 2 == 0, but only interpolants that refer to fixed values of a.
 * 
 * If we use BackwardPredicates we are able to prove correctness of this program.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 29.5.2014
 */

procedure proc();

implementation proc()
{
  var a: int;
  a := 0;
  while (*) {
	  a := a + 2;
  }
  assert a % 2 == 0;
//  assert a % 4 == 2 || a % 4 == 0;
}





  
