var x : int;

procedure inc() returns()
modifies x;
{
  if (x < 1) {
    assert x != 2;
  } else {
    assert x != 0;
  }
}

procedure ULTIMATE.start()
modifies x;
{
  fork 1 inc();
  join 1;
}
