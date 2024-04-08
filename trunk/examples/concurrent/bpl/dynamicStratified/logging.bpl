//#Safe
/*popl 23 example
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

procedure sum() returns (x : int)
modifies stdout, stdout_ptr;
{
  var i : int;

  x := 0;

  i := 0;
  while (i < N) {
    x := x + A[i];
    i := i + 1;

    // printf("Sum of first %d elements is %d", i, x);
    call log(i);
    call log(x);
  }
}

procedure ULTIMATE.start()
modifies stdout, stdout_ptr;
{
  var x, y : int;

  fork 1   sum();
  fork 2,2 sum();
  join 1   assign x;
  join 2,2 assign y;

  assert x == y;
}

