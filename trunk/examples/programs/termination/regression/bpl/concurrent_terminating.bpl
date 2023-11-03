//#Terminating
/**
 * This program is an example for a terminating concurrent program.
 *
 * Author: Frank Schüssele
 * Date: 2023-01-25
 */

var x, y : int;

procedure ULTIMATE.start()
modifies x, y;
{
  fork 1   decX();
  fork 2,2 decY();
  join 1;
  join 2,2;
}

procedure decX()
modifies x;
{
  while (x > 0) {
    x := x-1;
  }
}

procedure decY()
modifies y;
{
  while (y > 0) {
    y := y-1;
  }
}
