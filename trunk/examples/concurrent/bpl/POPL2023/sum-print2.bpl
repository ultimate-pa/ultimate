//#Safe
/*
 * Author: Dominik Klumpp
 * Date: June 2022
 */

// T1 commutes concretely against T2, T3; but not (lightweight-)abstract!
// T2, T3 commute (lightweight-)abstractly against each other (print must be abstracted); but not concretely
// T2, T3 need good loop-lockstep alignment for a simple proof!


var N : int;
var x, y : int;
var A : [int]int;

var buf : [int]int;
var idx : int;

var i, j, k : int;

procedure T2()
modifies x, i, buf, idx;
{
  while (*) {
    atomic {
      assume i < N;
      x := x + A[i];
      i := i + 1;
    }
    //atomic { call print(i); }
  }
}

procedure T3()
modifies x, i, buf, idx;
{
  while (*) {
    atomic {
      assume i < N;
      x := x + A[i];
      i := i + 1;
    }
    //atomic { call print(i); }
  }
}

procedure T4()
modifies y, k;
{
  k := 0;
  while (k < N) {
    y := y + A[k];
    k:= k + 1;
    if (k < N) {
      y := y + A[k];
      k:= k + 1;
    }
  }
}

procedure print(val : int)
modifies buf, idx;
{
  buf[idx] := val;
  idx := idx + 1;
}

procedure ULTIMATE.start()
modifies x, y, i, k, buf, idx;
{
  x := 0;
  y := 0;
  i := 0;

//  fork 1 T1();
  fork 2,2 T2();
  fork 3,3,3 T3();
  fork 4,4,4,4 T4();
//  join 1;
  join 2,2;
  join 3,3,3;
  join 4,4,4,4;

  assert i >= N ==> x == y;
}
