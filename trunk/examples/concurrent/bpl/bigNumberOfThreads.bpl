//#Unsafe

/*
 * We can prove this program incorrect for 5 threads, but we fail for bigger
 * numbers (like 10, 10000, ...), although the actual number does not matter.
 * The program is unsafe for any number of threads. A feasible error trace
 * forks all threads, but does not execute them at all. Therefore x remains 0.
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2021-05-26
 *
 */

var x: int;

procedure thread() returns()
modifies x;
{
  x := x + 1;
}

procedure ULTIMATE.start() returns()
modifies x;
{
  var i : int;
  x := 0;
  i := 0;

  while (i < 5) {
    fork i thread();
	i := i + 1;
  }
  assert x > 0;
}
