//#Termination
/*
 * Program from Fig.1 of
 * 2012SAS - Chen,Flur,Mukhopadhyay - Termination Proofs for Linear Simple Loops
 *
 * Date: 23.02.2014
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var x,y,z: int;

procedure main()
modifies x, y, z;
{
  while (x > 0) {
    x := x + y;
    y := z;
    z := -z - 1;
  }
}