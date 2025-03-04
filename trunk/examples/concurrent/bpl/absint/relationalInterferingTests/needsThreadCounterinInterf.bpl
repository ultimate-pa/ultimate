var x : int;

procedure ULTIMATE.start() returns()
modifies x;
{
  x := 0;
  fork 1 thread2();
  fork 2 thread1();
}

procedure thread1() returns()
modifies x;
{
  x := 1;
}

procedure thread2() returns()
modifies x;
{
  x := 2;
  assert x > 0;
}

