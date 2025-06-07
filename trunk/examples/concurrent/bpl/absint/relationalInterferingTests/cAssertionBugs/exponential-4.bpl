var y  : int;
var z  : int;
var x  : int;
var p  : int;
var i  : int;
var _N : int;

procedure ULTIMATE.start() returns ()
  modifies y, z, x, p, i, _N;
{
  _N := 4;
  p  := 0;

  while (p < _N)
  {
    fork 1 f1();
    fork 2 f2();
    p := p + 1;
  }

  z := 0;
  i := 0;
  while (i < _N)
  {
    assume z < 2147483647;
    z := z + 2 * y;
    i := i + 1;
  }

  if (z % 2 == 0) {
    x := 0;
  } else {
    x := 1;
  }

  assert x * y == 0;
}

procedure f1() returns ()
  modifies y;
{
  atomic {
    y := (y + 1) % 1073741823;
  }
}

procedure f2() returns ()
  modifies y;
{
  atomic {
    y := (2 * y) % 1073741823;
  }
}

