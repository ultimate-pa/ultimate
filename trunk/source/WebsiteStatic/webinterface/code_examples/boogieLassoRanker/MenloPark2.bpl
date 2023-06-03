//#rTermination
/*
 * Date: 18.12.2012
 * Author: Jan Leike and heizmann@informatik.uni-freiburg.de
 *
 * First comment by Matthias: (incorrect, see comment 2)
 * Has linear ranking function f(x)=x with supporting invariant y>=0.
 * But even over the integers, there is no linear ranking function with 
 * non-decreasing supporting invariant.
 * (So this is a counterexample to the relative completeness over the 
 * integers as discussed in Matthias talk.)
 * 
 * Second comment by Matthias:
 * Has linear ranking function f(x)=x with supporting invariant true.
 * The fact that y > 0 when subtracted from x follows from 
 * y < 7;y := - y + 7;
 * 
 * 
 */

procedure MenloPark() returns (x,y,z: int)
{
  assume(y >= 0);
  while (y < 7 && x >= 0) {
    y := - y + 7;
    x := x - y;
  }
}

