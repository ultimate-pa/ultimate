//#Safe

/*
 * Check that nested atomic statements are supported, and the entire (outer) atomic statement is executed atomically.
 *
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 2024-08-22
 *
 */

var x : int;

procedure ULTIMATE.start()
modifies x;
{
  x := 0;
  fork 1 thread();
  assert x == 0;
}

procedure thread()
modifies x;
{
  call __VERIFIER_atomic_begin();
    atomic { x := 1; x := 17; }
    x := 2;
    atomic { x := 17; x := 0; }
  call __VERIFIER_atomic_end();
}

procedure __VERIFIER_atomic_begin();
procedure __VERIFIER_atomic_end();
