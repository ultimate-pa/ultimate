var n, x : int;

procedure ULTIMATE.start()
modifies x;
{
  x := 1;

  fork 1 one();
  fork 2 two();
  fork 3 three();
  join 1;
  join 2;
  join 3;
}

procedure one()
modifies x;
{
  while (x == 1) {
    x := 2;
  }
}

procedure two()
modifies x;
{
  while (x == 2) {
    x := 3;
  }
}

procedure three()
modifies x;
{
  while (x == 3) {
    x := 1;
  }
}
