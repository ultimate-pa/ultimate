//#Safe
/*
 * Author: Dominik Klumpp
 * Date: 2022-05-27
 */

var stdout : [int]int;
var stdout_ptr : int;

var A : [int]int;
var N : int;

procedure log(msg : int)
modifies stdout, stdout_ptr;
{
  atomic {
    stdout[stdout_ptr] := msg;
    stdout_ptr := stdout_ptr + 1;
  }
}

procedure sum(lo : int, hi : int) returns (x : int, z : int)
modifies stdout, stdout_ptr;
{
  var i : int;

  x := 0;
  z := 0;

  i := lo;
  while (i < hi) {
    x := x + A[i];
    i := i + 1;
    z := if z + A[i] > 0 then z + A[i] else 0;

    // printf("Sum of first %d elements is %d, i, x);
    //call log(i);
    //call log(x);
  }
}

function max(a : int, b : int) returns (int) {
  if (a > b) then a else b
}

procedure ULTIMATE.start()
modifies stdout, stdout_ptr;
{
  var k1, k2, k3 : int;
  var s1, m1, s2, m2, s3, m3, s4, m4 : int;

  assume 0 <= k1 && k1 <= k2 && k2 <= k3 && k3 <= N;

  fork 1 sum(0, k1);
  fork 2,2 sum(k1+1, k2);
  fork 3,3,3 sum(k2+1, k3);
  fork 4,4,4,4 sum(k3+1, N);
  join 1 assign s1, m1;
  join 2,2 assign s2, m2;
  join 3,3,3 assign s3, m3;
  join 4,4,4,4 assign s4, m4;

  assert max(max(max(m4, s4 + m3), s4 + s3 + m2), s4 + s3 + s2 + m1) >= 0;
  //assert m4 >= 0;
}

