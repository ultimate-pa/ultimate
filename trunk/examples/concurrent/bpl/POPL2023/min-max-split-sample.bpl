//#Safe
/*
 * Benchmark for the combinationof (variable) abstraction with concrete commutativity:
 *
 * While computeMin and computeMax commute concretely, they only commute abstractly against the sample thread.
 *
 * Because computeMin and computeMax are disjoint, they in fact also commute under lightweight-abstract.
 * However, the two copies of computeMin (resp. computeMax) only commute against each other under heavyweight(-concrete) commutativity.
 *
 * Author: Dominik Klumpp
 * Date: 2022-06-08
 */

var A, B : [int]int;
var N : int;
var k : int;

var i1, i2, i3, i4 : int;
var array_min, array_max : int;
var min_samples, max_samples : [int]int;

function min(a : int, b : int) returns (int) {
  if (a < b) then a else b
}

function max(a : int, b : int) returns (int) {
  if (a < b) then b else a
}

procedure computeMin1()
modifies i1, array_min;
{
  i1 := 0;

  while (i1 < k) {
    atomic {
      array_min := min(array_min, A[i1]);
      i1 := i1 + 1;
    }
  }
}
procedure computeMin2()
modifies i2, array_min;
{
  i2 := k+1;

  while (i2 < N) {
    atomic {
      array_min := min(array_min, A[i2]);
      i2 := i2 + 1;
    }
  }
}

procedure computeMax1()
modifies i3, array_max;
{
  i3 := 0;

  while (i3 < k) {
    atomic {
      array_max := max(array_max, A[i3]);
      i3 := i3 + 1;
    }
  }
}

procedure computeMax2()
modifies i4, array_max;
{
  i4 := k+1;

  while (i4 < N) {
    atomic {
      array_max := max(array_max, A[i4]);
      i4 := i4 + 1;
    }
  }
}

procedure sample()
modifies min_samples, max_samples;
{
  while (*) {
    min_samples[i1-1] := array_min;
    min_samples[i2-1] := array_min;
    max_samples[i3-1] := array_max;
    max_samples[i4-1] := array_max;
  }
}

procedure ULTIMATE.start()
modifies i1, i2, i3, i4, array_min, array_max, min_samples, max_samples;
{
  assume 0 <= k && k <= N;

  array_min := A[0];
  array_max := A[0];

  fork 1         computeMin1();
  fork 2,2       computeMin2();
  fork 3,3,3     computeMax1();
  fork 4,4,4,4   computeMax2();
  fork 5,5,5,5,5 sample();
  join 1;
  join 2,2;
  join 3,3,3;
  join 4,4,4,4;

  assert array_min <= array_max;
}

