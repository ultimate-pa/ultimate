//#Safe
/*
 * Author: Dominik Klumpp
 * Date: June 2022
 */

var A, B : [int]int;
var N : int;

var i1, i2 : int;
var sum1, sum2 : int;

function abs(a : int) returns (int) {
  if (a < 0) then -a else a
}

procedure sum1() returns (x : int)
modifies i1, sum1;
{
  sum1 := 0;

  i1 := 0;
  while (i1 < N) { atomic {
    sum1 := sum1 + abs(A[i1]);
    i1 := i1 + 1;
  }}
}

procedure sum2() returns (y : int)
modifies i2, sum2;
{
  sum2 := 0;

  i2 := 0;
  while (i2 < N) { atomic {
    sum2 := sum2 + abs(A[i2]);
    i2 := i2 + 1;
  }}
}

procedure bank()
modifies B;
{
  while (*) { atomic {
    B[i1-1] := sum1;
    B[i2-1] := sum2;
  }}
}


procedure mapAbs()
modifies A;
{
  var j : int;

  j := 0;
  while (j < N) { atomic {
    A[j] := abs(A[j]);
    j := j + 1;
  }}
}

procedure ULTIMATE.start()
modifies A, B, i1, i2, sum1, sum2;
{
  fork 1 bank();
  fork 2,2 sum1();
  fork 3,3,3 sum2();
  fork 4,4,4,4 mapAbs();
  join 2,2;
  join 3,3,3;

  assert sum1 == sum2;
}

