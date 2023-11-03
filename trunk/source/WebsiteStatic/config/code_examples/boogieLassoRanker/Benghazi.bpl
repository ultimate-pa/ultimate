//#rTerminationDerivable
/*
 * Date: 18.11.2012
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Has ranking function f(x,d1,d2)=x for the invariant
 * d1 >=1 /\ d2>=1.
 * However, we are not able to derive such a (conjunctive) invariant.
 * 
 * Nonetheless this lasso program has some three phase ranking function.
 *
 */

procedure Benghazi(y: int) returns (x: int)
{
  var d1, d2:int;
  assume(d1 == 73);
  assume(d2 == 74);
  while (x >= 0) {
    x := x - d1;
    d1 := d2 + 1;
    d2 := d1 + 1;
  }
}
