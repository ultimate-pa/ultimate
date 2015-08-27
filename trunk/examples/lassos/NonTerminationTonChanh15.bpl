//#rNonTerminationDerivable
/*
 * Date: 2015-07-26
 * Author: Ton Chanh Le
 */

procedure main() returns (x: int, y: int)
{
  while (x >= 0) {
    x := x + y;
    y := y + 1;
  }
}

