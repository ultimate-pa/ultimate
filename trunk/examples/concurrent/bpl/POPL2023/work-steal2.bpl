//#Safe
/*
 * Simple sketch of a work-stealing benchmark.
 *
 * The idea is that the actions of different threads commute concretely, but only under the
 * condition that the accessed indices are indeed disjoint.
 *
 * If we only check that array accesses are within bounds, then we can abstract the array
 * contents, and under this abstraction, the accesses commute unconditionally.
 *
 * However, the "stealing" steps (reserving the next index for the current thread) do not
 * commute against each other! The order of such calls yields different (though symmetric)
 * states. Our abstractions are not able to achieve commutativity.
 *
 * Author: Dominik Klumpp
 * Date:   2022-05-23
 */

var A : [int]int;
var cnt : int;
var N : int;

procedure ULTIMATE.start()
modifies cnt, A;
{
  assume cnt == 0;
  assume N >= 0;

  fork 1   workerWithAssert();
  fork 2,2 worker();
}

procedure workerWithAssert()
modifies cnt, A;
{
  var i, sz : int;

  while (*) {
    call i, sz := steal(1);
    if (sz <= 0) {
      break;
    }
    assert 0 <= i && i < N; // index-out-of-bounds check
    A[i] := A[i] + 1;
  }
}

procedure worker()
modifies cnt, A;
{
  var i, sz : int;

  while (*) {
    call i, sz := steal(1);
    if (sz <= 0) {
      break;
    }
    assume 0 <= i && i < N; // index within bounds
    A[i] := A[i] + 1;
  }
}

procedure steal(delta : int) returns (x : int, num : int)
modifies cnt;
{
  // problematic: two such calls will not commute concretely, because the return values depend on the order (symmetry)
  atomic {
    if (cnt < N) {
      x := cnt;
      num := if N - cnt > delta then delta else N - cnt;
      cnt := cnt + num;
    } else {
      num := 0;
    }
  }
}
