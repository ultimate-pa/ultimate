//#Safe
/*
 * Author: Dominik Klumpp
 * Date: June 2022
 */

var N : int;
var x, y : int;
var A : [int]int;
var LOCK : [int]int;

var i, j : int;

procedure T1()
modifies x, y;
{
  while (*) {
    x := x + 1;
    y := y - 1;
  }
}

procedure T2()
modifies x, i, LOCK;
{
  i := 0;
  while (i < N) {
    atomic { call acq_read(i); }
    x := x + A[i];
    atomic { call rel_read(i); }
    i := i + 1;
  }
}

procedure T3()
modifies y, j, LOCK;
{
  j := 0;
  while (j < N) {
    atomic { call acq_read(j); }
    y := y + A[j];
    atomic { call rel_read(j); }
    j := j + 1;
  }
}

procedure acq_read(idx : int)
modifies LOCK;
{
  assume LOCK[idx] >= 0;
  LOCK[idx] := LOCK[idx] + 1;
}
procedure rel_read(idx : int)
modifies LOCK;
{
  LOCK[idx] := LOCK[idx] - 1;
}


procedure ULTIMATE.start()
modifies x, y, i, j, LOCK;
{
  x := 0;
  y := 0;

  fork 1 T1();
  fork 2,2 T2();
  fork 3,3,3 T3();
  join 1;
  join 2,2;
  join 3,3,3;

  assert x >= y;
}
