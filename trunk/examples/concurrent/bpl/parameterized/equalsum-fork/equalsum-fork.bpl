//#Safe

var A : [int]int;
var n : int;

var x, y, i, j, m : int;

procedure ULTIMATE.start()
modifies x,y;
{
  var c : int;

  assume 0 <= i && i < j && j < m;

  // fork m threads
  c := 0;
  while (c < m) {
    fork c thread(c);
    c := c + 1;
  }

  // join m threads
  c := 0;
  while (c < m) {
    join c;
    c := c + 1;
  }

  assert x == y;
}

procedure thread(id : int)
modifies x, y;
{
  var sum, idx : int;
  sum := 0;
  idx := 0;

  while (idx < n) {
    sum := sum + A[idx];
    idx := idx + 1;
  }

  if (id == i) {
    x := sum;
  }
  if (id == j) {
    y := sum;
  }
}
