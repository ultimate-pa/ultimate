var x, y : int;
var a, b, c : int;

procedure ULTIMATE.start()
modifies x,y;
{
  assume a >= 0 && b >= 0;
  fork 1 thread1();
  fork 2,2 thread2();
  join 1;
  join 2,2;

  assert (c == 0) ==> (x == y);
}

procedure thread1()
modifies x;
{
  var i : int;

  x := 0;
  i := 0;
  while (i < a) {
    x := x + b;
    i := i + 1;
  }
}

procedure thread2()
modifies y;
{
  var j : int;

  if (c == 0) {
    y := 0;
    j := 0;
    while (j < a) {
      y := y + b;
      j := j + 1;
    }
  }
}

