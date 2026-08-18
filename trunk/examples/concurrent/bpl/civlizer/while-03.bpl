var x : int;
var y : int;

procedure inc() returns()
modifies y;
{
  while (y < 10) {
    y := y + 1;
  }
}

procedure ULTIMATE.start()
modifies x, y;
{
  x := 0;

  fork 1 inc();
  join 1;

  assert x == 0;
}
