//#Safe

/*
 * We are unable to prove the program safe, because it has an unbounded number
 * of threads.
 * If we add the outcommented join, we can easily prove the program safe.
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2020-09-17
 *
 */

var x0: int;
var x1: int;

procedure thread1() returns()
modifies x0, x1;
{
  x1 := x0 + 1;
}
procedure ULTIMATE.start() returns()
modifies x0, x1;
{
  
  x0 := 0;
  x1 := 0;

  while (*) {
    fork 1 thread1();
  }

  assert x0 == 0 && x1 >= 0 ;
}
