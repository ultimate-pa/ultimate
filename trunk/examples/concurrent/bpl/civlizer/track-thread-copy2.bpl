var x : int;

procedure ULTIMATE.start()
modifies x;
{
  ​x := 0;
  fork 1 t();
  join 1;

  assert x == 1;
  fork 1 t(); // same template, same ID, but copy could be annotated with "true"
}

procedure t()
modifies x;
{
  x := x + 1;
}

