//#Safe
/*
 * Benchmark where (variable) abstraction is essential:
 *
 * While computeMin and computeMax commute concretely, they only commute abstractly against the sample thread.
 *
 * However, because computeMin and computeMax are disjoint, they in fact also commute under lightweight-abstract.
 *
 * Author: Dominik Klumpp
 * Date: 2022-06-08
 */

var A : [int]int;
var N : int;

var i1, i2 : int;
var array_min, array_max : int;
var min_samples, max_samples : [int]int;

function min(a : int, b : int) returns (int) {
  if (a < b) then a else b
}

function max(a : int, b : int) returns (int) {
  if (a < b) then b else a
}

procedure computeMin()
modifies i1, array_min;
{
  array_min := A[0];
  i1 := 0;

  while (i1 < N) {
    atomic {
      array_min := min(array_min, A[i1]);
      i1 := i1 + 1;
    }
  }
}

procedure computeMax()
modifies i2, array_max;
{
  array_max := A[0];
  i2 := 0;

  while (i2 < N) {
    atomic {
      array_max := max(array_max, A[i2]);
      i2 := i2 + 1;
    }
  }
}

procedure sample()
modifies min_samples, max_samples;
{
  while (*) {
    min_samples[i1-1] := array_min;
    max_samples[i2-1] := array_max;
  }
}

procedure ULTIMATE.start()
modifies i1, i2, array_min, array_max, min_samples, max_samples;
{
  fork 1     computeMin();
  fork 2,2   computeMax();
  fork 3,3,3 sample();
  join 1;
  join 2,2;

  assert array_min <= array_max;
}

