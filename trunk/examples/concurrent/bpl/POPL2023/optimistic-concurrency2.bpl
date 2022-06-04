//#Safe
/*
 * Benchmark inspired by optimistic concurrency control
 * <https://en.wikipedia.org/wiki/Optimistic_concurrency_control>
 *
 * Threads run possibly non-commuting actions in parallel.
 * Afterwards, check if there was a conflict, if yes roll back.
 *
 * But if we only check array accesses are within bounds,
 * we can abstract away the actual array contents.
 * Under this abstraction, the actions of different threads commute.
 *
 * Date: 2022-05-23
 * Author: Dominik Klumpp
 */


var A : [int]int;
var min1, max1, min2, max2 : int;
var N : int;

procedure reader(start : int, end : int) returns (sum : int)
{
  var i : int;

  sum := 0;
  i := start;
  while (i < end) {
    assume 0 <= i && i <= N; // index within bounds
    sum := sum + A[i];
    i := i + 1;
  }
}

procedure writer(start : int, end : int)
modifies A;
{
  var j : int;

  j := start;
  while (j < end) {
    assert 0 <= j && j <= N; // index-out-of-bounds check
    A[j] := 0;
    j := j + 1;
  }
}


procedure ULTIMATE.start()
modifies A;
{
  var min1, max1, min2, max2 : int;
  var sum : int;

  assume 0 <= min1 && max1 <= N;
  assume 0 <= min2 && max2 <= N;

  // Modify: run transactions in parallel
  fork 1   writer(min1, max1);
  fork 2,2 reader(min2, max2);
  join 1;
  join 2,2 assign sum;

  // Validate: Check if accessed data was also written
  if ((min1 <= max2 && min2 <= max1) || (min2 <= max1 && min1 <= max2)) {
    // Rollback (restart reader transaction)
    fork 2,2 reader(min2, max2);
    join 2,2 assign sum;
  }
}
