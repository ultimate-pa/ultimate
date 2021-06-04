//#Safe

/**
 * This program essentially aims to prove associativity of an implication of multiplication.
 * This is in general difficult, as non-linear assertions (z1 == x * y /\ z2 == y * x) are needed.
 * However, a partial order reduction may reduce the concurrent program to a lock-step interleaving
 * of the two concurrent loops, for which only linear arithmetic assertions are needed.
 *
 * Author: Dominik Klumpp
 * Date: 2021-06-04
 */

procedure ULTIMATE.start()
{
  var x, y, z1, z2 : int;
  assume x >= 0;
  assume y >= 0;

  fork 1   mult(x, y);
  fork 2,2 mult(y, x);
  join 1   assign z1;
  join 2,2 assign z2;

  assert z1 == z2;
}

procedure mult(a : int, b : int) returns (z : int) {
  var i : int;

  z := 0;
  i := 0;
  while (i < a) {
    z := z + b;
    i := i + 1;
  }
}
