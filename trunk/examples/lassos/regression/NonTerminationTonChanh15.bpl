//#rNonTerminationDerivable
/*
 * Date: 2015-07-26
 * Author: Jan Leike
 * This is a Boogie version of the program 2Nested_false-termination.c
 * which was submitted to the TermComp 2015 by Ton Chanh Le.
 */

procedure main() returns (x: int, y: int)
{
  while (x >= 0) {
    x := x + y;
    y := y + 1;
  }
}

