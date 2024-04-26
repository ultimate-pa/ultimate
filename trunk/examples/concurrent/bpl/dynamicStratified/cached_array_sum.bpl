/**
* Compute sum of array elements
* DSR pseudo-looplockstep
**/


var A : [int] int;

var result : int;
var flag : bool;
var N : int;

procedure ULTIMATE.start()
modifies result, flag;
{
  var x1, x2 : int;

  fork 1 worker(1);
  fork 2,2 worker(2);

  join 1 assign x1;
  join 2,2 assign x2;
  assert x1 == x2;
}

procedure worker(id : int)
returns (x : int)
modifies result, flag;
{
  var i : int;

  if (flag) {
    // computation already performed; use cached value and return
    x := result;

  } else {
    // computation not yet performed; perform it now and store result
    x := 0;
    i := 0;

    while (i < N) {
      x := x + A[i];
      i := i + 1;

      // store intermediate result; but don't overwrite correct result
	  atomic {
        if (!flag) { 
	      result := x; 
		} 
	  } 
    }

    // completed computation of result
    atomic { flag := true; result := x; }
  }
}
