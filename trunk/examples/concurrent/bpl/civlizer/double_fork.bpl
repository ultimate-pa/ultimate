var x : int;

procedure ULTIMATE.start()
modifies x;
{
  assume x == 0;

  fork 1 thread();
  join 1;
  fork 1 thread();
  join 1;

  assert x == 2;
}

procedure thread()
modifies x;
{
  x := x + 1;
}
