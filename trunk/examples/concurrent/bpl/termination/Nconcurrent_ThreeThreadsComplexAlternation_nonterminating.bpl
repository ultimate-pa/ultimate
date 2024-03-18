var x,n : int;

procedure ULTIMATE.start()
modifies x,n;
{
  x := 1;
  n := 1;

  fork 1 one();
  fork 2 two();
  fork 3 three();
  join 1;
  join 2;
  join 3;
}

procedure one()
modifies x,n;
{
  while (x == 1 && n < 4) {
    x := 2;
    n := n+1;
  }
}

procedure two()
modifies x;
{
  while (x == 2) {
    x := 1;
  }
}

procedure three()
modifies n;
{
  while (n == 3) {
    n := 1;
  }
}