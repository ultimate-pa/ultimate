//#Unsafe
/* Example that we discussed on Monday 12th May. The example shows that
 * our definition of relevancy for a havoc statement is not useful
 * (and does not coinicde with our algorithm).
 * 
 * It is not sufficient to replace havoc with assignment that has
 * a value on the rhs, we need to allow an expression on the rhs.
 * Because we have to choose for y the same value as for x.
 * 
 * Author: Christian Schilling, Matthias Heizmann, Numair Mansur
 * Date: 2017-06-12
 * 
 * 
 */

procedure main() returns () {
  var x, y : int;
  havoc x;
  havoc y;
  assume(x != y);
  assert(false);
}


