//#rNonTermination
/*
 * Date: 2015-09-01
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * This is a Boogie version of the program Hanoi_plus_false-termination.c
 * which was submitted to the TermComp 2015 by Ton Chanh Le.
 * 
 * We cannot solve it because Z3 runs into a timeout.
 * 
 */

procedure main() returns ()
{
  var x, y, z: real;
  while (x > 0.0) {
    x := x + y;
    y := y + z;
    z := z + x;
  }
}

