//#Safe
/*
 * Benchmark intended to showcase one aspect of variable abstraction:
 * By abstracting irrelevant variables, additional commutativity can be gained.
 * Such additional commutativity can indeed simplify the proof; in this case by allowing us to exactly align the loop iterations of both threads.
 *
 * In this case, the irrelevant computation being abstracted is the logging.
 * The idea is that even in realistic programs, non-commutative (concretely) logging calls might indeed occur,
 * as the programmer does not care in which order data is logged.
 * Whereas non-commutative (concretely, even contextually) statements that compute actually important results are probably not too common in correct programs.
 *
 * Author: Dominik Klumpp
 * Date: 2022-05-23
 */

var stdout : [int]int;
var stdout_ptr : int;

var A : [int]int;
var N : int;

procedure log(msg : int)
modifies stdout, stdout_ptr;
{
  atomic {
    stdout[stdout_ptr] := msg;
    stdout_ptr := stdout_ptr + 1;
  }
}

procedure sum() returns (x : int)
modifies stdout, stdout_ptr;
{
  var i : int;

  x := 0;

  i := 0;
  while (i < N) {
    x := x + A[i];
    i := i + 1;

    // printf("Sum of first %d elements is %d", i, x);
    call log(i);
    call log(x);
  }
}

procedure ULTIMATE.start()
modifies stdout, stdout_ptr;
{
  var x1, x2, x3 : int;

  fork 1           sum();
  fork 2,2         sum();
  fork 3,3,3       sum();
  join 1           assign x1;
  join 2,2         assign x2;
  join 3,3,3       assign x3;

  assert x1 == x2 && x2 == x3;
}

