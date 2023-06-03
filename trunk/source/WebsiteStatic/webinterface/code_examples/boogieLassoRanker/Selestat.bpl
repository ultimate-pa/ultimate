//#rNonTermination
/*
 * Date: 18.02.2012
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure Selestat(c: int) returns (x: int)
{
  var y: int;

  assume true;
  while (x >= 0) {
    x := x + 1;
  }
}

