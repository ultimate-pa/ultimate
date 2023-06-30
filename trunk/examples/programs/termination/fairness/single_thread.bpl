//#Nonterminating

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2023-06-29
 *
 */

var x: int;

procedure thread() returns()
modifies x;
{
  while (x > 0) {
    x := x + 1;
  }
}

procedure ULTIMATE.start() returns()
modifies x;
{
  fork 0 thread();
}
