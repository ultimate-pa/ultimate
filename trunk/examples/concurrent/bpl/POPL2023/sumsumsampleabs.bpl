//#Safe

var A, B : [int]int;
var N : int;

var i1, i2 : int;
var sum1, sum2, array_min, array_max : int;


function abs(a : int) returns (int) {
  if (a < 0) then -a else a
}
function min(a : int, b : int) returns (int) {
  if (a < b) then a else b
}

function max(a : int, b : int) returns (int) {
  if (a < b) then b else a
}


procedure sum1() returns (x : int)
modifies i1, sum1, array_min;
{
  sum1 := 0;
  array_min := A[0];

  i1 := 0;
  while (i1 < N) {

    sum1 := sum1 + abs(A[i1]);
      array_min := min(array_min, A[i1]);
    i1 := i1 + 1;

  }
}

procedure sum2() returns (y : int)
modifies i2, sum2, array_max;
{
  sum2 := 0;
  array_max := A[0];

  i2 := 0;
  while (i2 < N) {

    sum2 := sum2 + abs(A[i2]);
      array_max := max(array_max, A[i2]);
    i2 := i2 + 1;

  }
}

procedure bank()
modifies B;
{
  while (*) {
    B[i1-1] := array_min;
    B[i2-1] := array_max;
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

procedure ULTIMATE.start()
modifies A, B, i1, i2, sum1, sum2, array_min, array_max;
{
  var x, y : int;

  fork 1   sum1();
  fork 2,2 sum2();
  fork 4,4,4,4 mapAbs();
  fork 3,3,3 bank();
  join 1;
  join 2,2;

  assert sum1 == sum2;
}

