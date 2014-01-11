//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 5.5.2012
 * 
 * Safe, but uses non-linear arithmetic.
 * State in revision r5962: We return an UnprovableResult because SmtInterpol
 * and Z3 do not support non-linear arithmetic.
 */

procedure proc();

implementation proc()
{
  var x: int;
  x := 2;
  x := x*x;
  assert (x == 4);
}




  
