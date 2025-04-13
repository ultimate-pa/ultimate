var x : int;

procedure ULTIMATE.start() returns()
modifies x;
{
  x := 0;
  fork 1 thread1();
}

procedure thread1() returns()
modifies x;
{
  x := 1;
  assert x == 1;
}
