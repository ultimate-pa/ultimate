//#Safe
/*
This program illustrates the effectiveness of POR to reduce proof size.

Without any reduction, the number of required assertions is exponential in the
number of thread instances: For each set of thread instances, we require the
assertion that "x = the sum of the respective threads' local variables t".
Ultimate can prove the program correct for 3 threads in a few seconds, but does
not terminate within 60min for 4 or more threads (Petri net toolchain).

If sleep-set POR is performed, a linear number of assertions is sufficient,
namely "x = t" for each thread instance's local variable t.

With Lipton reduction / Petri net LBE, each thread instance becomes atomic
(equivalent to "skip") and the single assertion "x = 0" suffices. Ultimate
requires less than 1s for 4 threads.
*/

var x : int;

procedure Thread() returns()
modifies x;
{
  var t : int;
  havoc t;
  x := x + t;
  x := x - t;
}

procedure ULTIMATE.start() returns()
modifies x;
{
  x := 0;

  fork 1 Thread();
  fork 2 Thread();
  fork 3 Thread();
  fork 4 Thread();

  join 1;
  join 2;
  join 3;
  join 4;

  assert x == 0;
}
