//#Safe

var A : [int]int;
var n : int;

var id_ctr : int;
var i, sum_i : int;
var terminated_i : bool;

procedure ULTIMATE.start()
free requires !terminated_i;
modifies id_ctr, sum_i, terminated_i;
{
  var id, sum, idx : int;
  atomic { id := id_ctr; id_ctr := id_ctr + 1; }

  sum := 0;
  idx := 0;

  while (idx < n) {
    sum := sum + A[idx];
    idx := idx + 1;
  }

  atomic {
    if (id == i) {
        sum_i := sum;
        terminated_i := true;
    }
  }
  assert (terminated_i ==> sum == sum_i);
}
