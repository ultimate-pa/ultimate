var x : int;

procedure inc() returns()
modifies x;
{
  while (x < 1) {
    x := x + 1;
  }
}

procedure ULTIMATE.start()
modifies x;
{
  x := 0;

  fork 1 inc();
  join 1;

  assert x == 1;
}
