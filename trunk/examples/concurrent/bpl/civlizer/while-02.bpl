var x : int;

procedure inc() returns()
{
  var y : int;
  while (y < 10) {
    y := y + 1;
  }
}

procedure ULTIMATE.start()
modifies x;
{
  x := 0;

  fork 1 inc();
  join 1;

  assert x == 0;
}
