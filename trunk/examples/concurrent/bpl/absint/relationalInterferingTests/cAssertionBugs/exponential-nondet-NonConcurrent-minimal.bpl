var x : int;
var y : int;

procedure ULTIMATE.start() returns()
modifies x, y;
{
  havoc y;

  if (y % 2 == 0) {
    x := 0;
  } else {
    x := 1;
  }

  assume x * y == 0;
}

