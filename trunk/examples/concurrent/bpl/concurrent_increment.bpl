//#Safe

/**
 * This program demonstrates that POR can lead to simpler proofs:
 * A Floyd-Hoare proof for the entire program needs very complicated assertions.
 * But as everything commutes, POR can reduce the program to lock-step interleaving,
 * leading to a much simpler proof with (essentially) only the assertions x==0, x==1, x==-1.
 *
 * Author: Dominik Klumpp
 * Date: 2021-06-04
 */

var n, x : int;

procedure ULTIMATE.start()
modifies x;
{
  x := 0;

  fork 1   inc();
  fork 2,2 dec();
  join 1;
  join 2,2;

  assert x == 0;
}

procedure inc()
modifies x;
{
  var i : int;
  i := 0;
  while (i < n) {
    x := x+1;
    i := i+1;
  }
}

procedure dec()
modifies x;
{
  var i : int;
  i := 0;
  while (i < n) {
    x := x-1;
    i := i+1;
  }
}
