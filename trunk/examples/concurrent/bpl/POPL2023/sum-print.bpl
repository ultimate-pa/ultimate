var N : int;
var x, y : int;
var A : [int]int;

var buf : [int]int;
var idx : int;

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
modifies x, i, buf, idx;
{
  i := 0;
  while (i < N) {
    x := x + A[i];
    atomic { call print(i); }
    i := i + 1;
  }
}

procedure T3()
modifies y, j, buf, idx;
{
  j := 0;
  while (j < N) {
    y := y + A[j];
    atomic { call print(j); }
    j := j + 1;
  }
}

procedure print(val : int)
modifies buf, idx;
{
  buf[idx] := val;
  idx := idx + 1;
}

procedure ULTIMATE.start()
modifies x, y, i, j, buf, idx;
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
