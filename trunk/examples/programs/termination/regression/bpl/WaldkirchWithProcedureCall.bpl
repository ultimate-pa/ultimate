//#Terminating
/*
 * Date: 18.02.2012
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(x) = x
 * Revealed different bugs in nested interpolation and tree interpolation in
 * r10009.
 *
 */

procedure Waldkirch(c: int) returns (x: int)
{
  assume true;
  while (x >= 0) {
    call doNothing();
    x := x - 1;
  }
}


procedure doNothing() returns()
{
}
  

