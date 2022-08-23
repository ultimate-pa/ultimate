//#Safe
/*
 * Idea: thread1 and thread2 full commute up to concrete-SMT; B can be abstracted away so that thread2 also commutes abstract-lightweight against thread3.
 *
 * Principle: thread1 performs map(A, f)
 *            thread2 performs aggr(A, B)
 *            thread3 performs update(B)
 *            such that map(_, f) and aggr(_, B) commute concretely (SMT);
 *            while aggr(A, _) and update(_) do NOT commute concretely but B is irrelevant for the spec.
 *
 *            other instances:
 *            f      aggr            update     property
 *            ---------------------------------------------------------
 *            relU   max_pos_index   :=k        A[m]>0 ==> result >= m
 *            abs    sum_abs         :=0        result >= |A[m]|
 *            abs    cnt_zeroes      :=0        ...
 *            abs    max_zero_index  :=0        ...
 *
 * Author: Dominik Klumpp
 * Date: June 2022
 */

var A, B : [int]int;
var N : int;

function abs(x : int) returns (int) { if x < 0 then -x else x }

procedure ULTIMATE.start()
modifies A, B;
{
  var m, result : int;
  assume 0 <= m && m < N;

  fork 1     thread1();
  fork 2,2   thread2();
  fork 3,3,3 thread3();
  join 1;
  join 2,2 assign result;
  join 3,3,3;

  assert A[m] == 0 ==> result >= 1;
}

// map A abs
procedure thread1()
modifies A;
{
  var i : int;

  i := 0;
  while (i < N) {
    A[i] := abs(A[i]);
    i := i + 1;
  }
}

// count indices with value 0 in A or B
procedure thread2() returns (cnt : int)
{
  var j : int;

  cnt := -1;

  j := 0;
  while (j < N) {
    if (A[j] == 0) {
      cnt := cnt + 1;
    }
    if (B[j] > 0) {
      cnt := cnt + 1;
    }

    j := j + 1;
  }
}

procedure thread3()
modifies B;
{
  var k : int;

  k := 0;
  while (k < N) {
    B[k] := k;
    k := 0;
  }
}
