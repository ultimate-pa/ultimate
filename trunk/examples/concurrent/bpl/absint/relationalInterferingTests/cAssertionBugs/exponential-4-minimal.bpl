//#Unsafe

var x : int;
var y : int;

procedure ULTIMATE.start() returns ()
modifies x, y;
{
  y := 0;

  fork 1 th_inc();

  if (y % 2 == 0) { x := 0; } else { x := 1; }

  assume x * y == 0;
}

procedure th_inc() returns ()
modifies y;
{
  atomic { y := y + 1; }
}

