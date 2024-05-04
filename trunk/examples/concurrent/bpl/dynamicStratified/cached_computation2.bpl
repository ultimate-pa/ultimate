//#Safe
// GPP verifies  (12 Iterations LoopLockstep, 11 Iteration for PseudoLockstep)
/**
  * Example where two threads perform same computation. When a thread finishes the computation, it stores the result in global variable (result),
  * and sets a flag to indicate the computation has been performed and the result has been cached.
  * If another thread then later sees that the flag has been set (ie the cache was initialized), it does not perform the computation again
  * but uses the cached result instead.
  * We show the property that no matter the interleaving, the two threads will always use the same value.
  *
  * The challenge lies in the fact that the invariant needed to prove two computations give the same result is very difficult.
  * Furthermore, intermittent checks to see if the value has become available in the meantime do not commute with the other thread's announcement of the cached value,
  * thus preventing a suitable reduction.
  *
  * However, we can split the analysis in two cases:
  * Case 1: If one of the threads uses the cached value, it is easy to see that the values are equal.
  *         For this case, the proof must refer to the cache variable ("result").
  * Case 2: If neither thread uses the cached value, then a proof need not refer to the cache variable "result".
  *         In this case, we can abstract the "result" variable, derive more commutativity, and we get a reduction with a simple invariant.
  */

var result : int;
var flag : bool;
var N : int;

procedure ULTIMATE.start()
modifies result, flag;
{
  var x1, x2 : int;

  fork 1 worker(1);
  fork 2,2 worker(2);

  join 1 assign x1;
  join 2,2 assign x2;
  assert x1 == x2;
}

procedure worker(id : int)
returns (x : int)
modifies result, flag;
{
  var i : int;

  if (flag) {
    // computation already performed; use cached value and return
    x := result;

  } else {
    // computation not yet performed; perform it now and store result
    x := 0;
    i := 0;

    while (i < N) {
      x := x + i;
      i := i + 1;

      // stop the computation if another thread has computed the value in the meantime
      if (flag) {
        x := result;
        return;
      }
    }

    // completed computation of result
    result := x;
    flag := true;
  }
}
