//#Safe
var x : int;

procedure ULTIMATE.start()
modifies x;
{
  x := 0;

  fork 1 Thread();
  join 1;

  assert x == 0;
}

procedure Thread()
modifies x;
{
  while (*) {
    x := x + 1;
    x := x - 1;
  }
}
