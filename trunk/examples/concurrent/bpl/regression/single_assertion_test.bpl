//#Unsafe
/*
 * This program illustrates that reachability of error locations depends on the number of thread instances:
 *
 * (a) An error location may only be reachable if sufficient thread instances exist.
 * (b) An error location may only be unreachable if sufficient thread instances exist.
 *
 * Note: If ALL error locations are unreachable for some number of thread instances (including the "insufficient threads" error locations),
 *       then ALL error locations will be unreachable for any higher number of thread instances as well.
 *       Point (b) does not contradict this.
 */

var x : int;

procedure ULTIMATE.start()
modifies x;
{
  var i : int;
  x := 0;

  i := 0;
  while (i < 2) {
    // "insufficient threads" error reachable if < 2 thread instances
    fork i thread(i);
    i := i + 1;
  }

  join 1;
  join 2;

  // assertion holds, but proof requires fact that there are 2 thread instances
  assert x >= 2;
}

procedure thread(i : int)
modifies x;
{
  x := x + 1;

  // assertion can be violated, but only with 2 or more thread instances
  assert i == 0;
}
