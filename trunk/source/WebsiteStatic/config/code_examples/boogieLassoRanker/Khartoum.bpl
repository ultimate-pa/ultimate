//#rTermination
/*
 * After one loop iteration, f(x, y) = x is a ranking function.
 * 
 * Date: 2012-04-01
 *
 */

procedure Khartoum() returns (x: int, y: int)
{
  assume true;
  while (x > 0) {
    x := x - y;
    y := 1;
  }
}

