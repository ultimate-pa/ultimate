//#Safe

/*
 * We are unable to prove the program safe, because it has an unbounded number
 * of threads.
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2021-04-26
 *
 */

var g: int;
var m: int;

procedure thread() returns()
modifies g, m;
{
  atomic { assume m == 0; m := 1; }
  g := g + 1;
  g := g - 1;
  m := 0;
}

procedure ULTIMATE.start() returns()
modifies g, m;
{
  g := 0;
  m := 0;
  
  while (*) {
    fork 0 thread();
  }
  
  assert m != 0 || g == 0;
}
