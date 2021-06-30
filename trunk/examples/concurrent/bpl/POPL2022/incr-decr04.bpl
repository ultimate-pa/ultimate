//#Safe
var x : int;

procedure ULTIMATE.start()
modifies x;
{
  x := 0;

  fork 1 Thread();
  fork 2,2 Thread();
  fork 3,3,3 Thread();
  fork 4,4,4,4 Thread();
  join 1;
  join 2,2;
  join 3,3,3;
  join 4,4,4,4;

  assert x == 0;
}

procedure Thread()
modifies x;
{
  while (*) {
    x := x + 1;
    x := x - 1;
  }
}
