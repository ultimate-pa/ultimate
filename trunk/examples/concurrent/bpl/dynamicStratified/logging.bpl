//#Safe
/*
 * array-sum-with-log from popl 23 modified to fit only dsr
 */

var stdout : [int]int;
var stdout_ptr : int;

var A : [int]int;
var N, z, c : int;

procedure ULTIMATE.start()
modifies stdout, stdout_ptr, z;
{
  var x, y : int;
  z := 0;
  fork 1   sum();
  fork 2,2 sum_z();
  join 1   assign x;
  join 2,2 assign y;

  assert (c == 0) ==> (x == y);
}


procedure log(msg : int)
modifies stdout, stdout_ptr, z;
{
  atomic {
    stdout[stdout_ptr] := msg;
    stdout_ptr := stdout_ptr + 1;
  }
  z := z + 1;
}

procedure sum() returns (x : int)
modifies stdout, stdout_ptr, z;
{
  var i : int;
  x := 0;

  i := 0;
  while (i < N) {
    x := x + A[i];
    i := i + 1;
	z := z + 1;
    // printf("Sum of first %d elements is %d", i, x);
    call log(i);
    call log(x);
  }
}

procedure sum_z() returns (x : int)
modifies z, stdout, stdout_ptr;
{  var i : int;
  x := 0;

  i := 0;
  if (c == 0) {
    while (i < N) {
      x := x + A[i];
      i := i + 1;
	  z := z + 1;
      call log(i);
      call log(x);
    }
  } else {
  z := 0;
  assert z != -1;
  }
}
	


