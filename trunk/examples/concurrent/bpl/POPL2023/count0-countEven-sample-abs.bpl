//#Safe
/*
 * Benchmark for combined concrete-abstract reduction.
 *
 * - The threads countZero and countEven commute concretely (they are disjoint).
 * - The thread mapAbs commutes concretely with countZero and countEven (the absolute value of an even number / of zero is even / is zero).
 * - The thread sample does not commute concretely with countZero and countEven, but it commutes abstractly (the variable diff can be abstracted away).
 *
 * Author: Dominik Klumpp
 * Date: 2022-06-08
 */

var A : [int]int;
var N : int;

var cntZero, cntEven : int;

function abs(a : int) returns (int) {
  if (a < 0) then -a else a
}

function { :smtdefined "((_ divisible 2) a)" } even(a : int) returns (bool);

procedure countZero()
modifies cntZero;
{
  var i1 : int;

  cntZero := 0;
  i1 := 0;

  while (i1 < N) {
    if (A[i1] == 0) {
      cntZero := cntZero + 1;
    }
    i1 := i1 + 1;
  }
}

procedure countEven()
modifies cntEven;
{
  var i2 : int;

  cntEven := 0;
  i2 := 0;

  while (i2 < N) {
    if (even(A[i2])) {
      cntEven := cntEven + 1;
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
  diff := cntEven - cntZero;
}

procedure ULTIMATE.start()
modifies cntZero, cntEven, A;
{
  fork 1       countZero();
  fork 2,2     countEven();
  fork 3,3,3   sample();
  fork 4,4,4,4 mapAbs();
  join 1;
  join 2,2;

  assert cntZero <= cntEven;
}

