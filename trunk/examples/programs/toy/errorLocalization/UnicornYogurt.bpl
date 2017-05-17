//#Unsafe
/*
 * The assume statement is "restrictive".
 * If we replace the (obviously relevant) assignment by a havoc we have more
 * "blocked executions", however there are not more assume statements that
 * become restrictive.
 * 
 * Author: Matthias Heizmann
 * Date: 2017-05-17
 * 
 * 
 */

procedure main() returns () {
  var x, y : int;
  y := 42;
  havoc x;
  assume(x >= 0 && y >= 23);
  assert(false);
}


