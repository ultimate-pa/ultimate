//#rTerminationDerivable
/*
 * Date: 2012-04-01
 *
 * Ranking function f(x, y) = x
 *
 */

procedure Kinshasa() returns (x: int, y: int)
{
  assume true;
  while (x > 0) {
    y := 1;
    x := x - y;
  }
}

