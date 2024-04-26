

// DSR PLS works in 8 It, LLS not in 13 It.
// Doesn't work for GPP 
/**
* Use two different computation methods to compute something. Prove that the end result of both methods is the same.
* same endpoints
* 
**/

var N, M : int;
var x1, x2 : int;
var c : int;

procedure ULTIMATE.start()
modifies x1, x2, c;
{
  c := N;
  x1 := 1;
  x2 := 1;
  fork 1 comp_1();
  fork 2,2 comp_2();

  join 1;
  join 2,2;
  assert (N == M) ==> (x1 == x2 && (c == N || c == 3 * M));
}


procedure comp_1()
modifies x1, c;
{
  var i : int;
  i := 0;
  while (i < N) {
	x1 := 2 * x1;
    i := i + 1;
	// something that only commutes when we can abstract i and j
	c := i;

  }
}

procedure comp_2()
modifies x2, c;
{
  var i : int;
  i := 0;

  while (i < 3 * M) {
	x2 := x2 + x2;
    i := i + 3;
	// something that only commutes when we can abstract i and j
	c := i;
  }
}
