//#rTerminationDerivable
/*
 * Date: 14.12.2012
 * Author: Jan Leike and heizmann@informatik.uni-freiburg.de
 *
 * Has linear ranking function f(x)=x with supporting invariant
 * (y>=100 /\ z=1) \/ (y>=99 /\ z=1).
 * However, there is no linear supporting invariant for this ranking function.
 * 
 * Has some three phase ranking function.
 */

procedure MenloPark() returns (x,y,z: int)
{
  y := 100;
  z := 1;
  while (x >= 0) {
    x := x - y;
    y := y - z;
    z := -z;
  }
}

