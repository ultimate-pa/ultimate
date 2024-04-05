var x, y : int;
var a, b, c : int;

procedure ULTIMATE.start()
modifies x,y;
{
  assume a >= 0 && b >= 0;
  fork 1 thread1();
  join 1;

  assert (c == 0) ==> (x == y);
}

procedure thread1()
modifies x,y;
{
  var i : int;
  var j : int;
  
  x := 0;
  i := 0;
  j := 0;
  while (i < a) {
    x := x + b;
    i := i + 1;
  }
  if (c == 0) {
    y := 0;
    j := 0;
    while (j < a) {
      y := y + b;
      j := j + 1;
    }
  }
}

