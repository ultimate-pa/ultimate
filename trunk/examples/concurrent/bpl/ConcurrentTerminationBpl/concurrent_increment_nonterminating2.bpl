/**
 * This program is an example for a non-terminating concurrent program.
 *
 * Author: Frank Schüssele
 * Date: 2022-06-28
 */

var n, x : int;

procedure ULTIMATE.start()
modifies x;
{
  x := -2;

  fork 1   dec();
  fork 2,2 inc();
  join 1;
  join 2,2;
}

procedure dec()
modifies x;
{
  while (x > -1) {
    x := x-1;
  }
}

procedure inc()
modifies x;
{
  while (x < 0) {
    x := x+1;
  }
}
