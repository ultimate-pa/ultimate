//#Safe
/*
 * Author: Dominik Klumpp
 * Date: 2022-06-08
 */

var A : [int]int;
var N : int;

var array_min, array_max : int;

function min(a : int, b : int) returns (int) {
  if (a < b) then a else b
}

function abs(a : int) returns (int) {
  if (a < 0) then -a else a
}

procedure computeMin()
modifies array_min;
{
  var i1 : int;

  array_min := A[0];
  i1 := 0;

  while (i1 < N) {
    if (abs(A[i1]) < array_min) {
      array_min := abs(A[i1]);
    }
    i1 := i1 + 1;
  }
}

procedure computeMax()
modifies array_max;
{
  var i2 : int;

  array_max := A[0];
  i2 := 0;

  while (i2 < N) {
    if (abs(A[i2]) > array_max) {
      array_max := abs(A[i2]);
    }
    i2 := i2 + 1;
  }
}

procedure mapAbs()
modifies A;
{
  var j : int;

  j := 0;
  while (j < N) {
    A[j] := abs(A[j]);
    j := j + 1;
  }
}

procedure sample() returns (diff : int)
{
  var min_l, max_l : int;

  while (*) {
  min_l := array_min;
  max_l := array_max;

  diff := max_l - min_l;
  }
}

procedure ULTIMATE.start()
modifies array_min, array_max, A;
{
  fork 1       computeMin();
  fork 2,2     computeMax();
  fork 3,3,3   sample();
  fork 4,4,4,4 mapAbs();
  join 1;
  join 2,2;
  join 3,3,3;
  join 4,4,4,4;

  assert array_min <= array_max;
}

