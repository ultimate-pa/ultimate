procedure ULTIMATE.start() returns ()
{
  while (true) {
    fork 1 worker();
  }
}

procedure worker() returns ()
{
  var e : int;
  e := 1;
  e := 2;
  assert e == 2;
}

