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
  var k1 : int;
  var s1, m1, s2, m2 : int;
  
  assume 0 <= k1 && k1 <= N;

  fork 1 sum(0, k1);
  fork 2,2 sum(k1+1, N);
  join 1 assign s1, m1;
  join 2,2 assign s2, m2;

  assert max(m2, s2 + m1) >= 0;
  //assert m2 >= 0;
}

