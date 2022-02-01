//#Unsafe
/*====== OLD DEFINITION COMMENTS===========
 * The assume statement is "restrictive".
 * If we replace the (obviously relevant) assignment by a havoc we have more
 * "blocked executions", however there are not more assume statements that
 * become restrictive.
 * 
 * Author: Matthias Heizmann
 * Date: 2017-05-17
 * ========================================
 *
 * As of our new definition on 25 June, only havoc x is relevant since 
 * there is no assignment to y that can make an existing execution of 
 * the error trace blocking.
 *
 * Coment added on : 2017-06-27
 * 
 */

procedure main() returns () {
  var x, y : int;
  y := 42;
  havoc x;
  assume(x >= 0 && y >= 23);
  assert(false);
}


