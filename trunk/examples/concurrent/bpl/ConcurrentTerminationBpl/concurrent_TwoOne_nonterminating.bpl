var n, x : int;

procedure ULTIMATE.start()
modifies x;
{
  x := 1;

  fork 1 double();
  fork 2 once();
  join 1;
  join 2;
}

procedure double()
modifies x;
{
  while (x < 4) {
    x := x+1;
  }
}

procedure once()
modifies x;
{
  while (x == 3) {
    x := 1;
  }
}