//#rTermination
/*
 * We fail to show termination because we do not compute the integral hull
 * for the constraints.
 * While proprocessing the division the assignment
 *     y := (y + 1) / 2;
 * is translated to the following transition contstraint (simplified by 
 * eliminating auxiliary variables)
 *     y' * 2 <= y + 1    /\    y' * 2 >= y
 * Over the integers, y >= 1 is invariant over this contstraint.
 * However, for applying Motzkin's theorem we consider these constraints over
 * the reals. There, y >= 1 is not invariant (y'=0.5 is also a solution).
 * 
 * Date: 2016-08-02
 * Author: heizmann@informatik.uni-freiburg.de
 */

procedure main() returns ()
{
  var x, y: int;
  y := 2;
  while (x >= 0) {
    x := x - y;
    y := (y + 1) / 2;
  }
}

