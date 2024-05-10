/*
Doesn't work
Added a z to the first assertion to sabotage global projection to the proof.
Result: GP does not abstract c, DSR does
*/
var x, y, z : int;
var a, b, c : int;

procedure ULTIMATE.start()
modifies x,y,z;
{
  z := 0;
  assume a >= 0 && b >= 0;
  fork 1 thread1();
  fork 2,2 thread2();
  join 1;
  join 2,2;

  assert (c == 0) ==> (x == y) && z != -1;
}

procedure thread1()
modifies x,z;
{
  var i : int;

  x := 0;
  i := 0;
  while (i < a) {
    x := x + b;
    i := i + 1;
    z := z + z;
  }
}

procedure thread2()
modifies y,z;
{
  var j : int;

  if (c == 0) {
    y := 0;
    j := 0;
    while (j < a) {
      y := y + b;
      j := j + 1;
      z := z + 1;
    }
  } else {
    z := 0;
    assert z != 1;
  }
}

