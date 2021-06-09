//#Unsafe

/**
 * Exposes a bug that occurred when a thread other than the main thread assigns the return value of a join to a global variable.
 * Ultimate tried to find the corresponding local variable in the thread instance (= copy of the thread template), failed to do so,
 * and crashed with a NullPointerException.
 *
 * Author: Dominik Klumpp
 * Date: 2021-06-10
 */

var x : int;

procedure ULTIMATE.start()
modifies x;
{
  fork 0 thread0();
  fork 1, 1 thread1();
  x := 0;
  assert x == 0;
}

procedure thread0() returns (z : int)
{
  z := 1;
}

procedure thread1()
modifies x;
{
  join 0 assign x;
}
