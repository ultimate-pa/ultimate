//#rTermination
/*
 * Date: 21.09.2013
 * Author: leike@informatik.uni-freiburg.de
 *
 * This is the program "ERRATIC" from Fig.1 of
 * A. R. Bradley, Z. Manna, and H. B. Sipma.
 * The Polyranking Principle.
 * In ICALP, pages 1349–1361. Springer, 2005.
 *
 * This program has a lexicographic multiphase ranking function.
 */

procedure main(N: int) returns (x: int, y: int)
{
  var p: int;
  var q: int;
  var n: int;
  var e: int;

  var x_old, y_old, n_old, e_old, q_old: int;
  assume(p >= 0 && q >= 1 && x == 0 && y == 0);
  while (true) {
    x_old := x;
    y_old := y;
    n_old := n;
    e_old := e;
    
    if (*) {
      assume(x + y <= N);
      havoc x;
      assume(x_old + e_old - q <= x && x <= x_old + e_old + q);
      havoc y;
      assume(y_old + n_old - q <= y && y <= y_old + n_old + q);
      havoc n;
      havoc e;
      assume(n_old + e_old + 1 <= n + e && n + e <= n_old + e_old + p);
    } else if (*) {
      assume(x + y <= N && n + e >= 2*q + 1);
      havoc x;
      assume(x_old + e_old - q <= x && x <= x_old + e_old + q);
      havoc y;
      assume(y_old + n_old - q <= y && y <= y_old + n_old + q);
    } else {
      assume(p >= 0);
      havoc n;
      havoc e;
      assume(n + e <= -(n_old + e_old));
      p := p - 1;
      q_old := q;
      havoc q;
      assume(2*q == q_old); // q := q / 2;
    }
  }
}
