//#Safe

var x : int;

procedure thread()
free requires x == 0;
modifies x;
{
  x := x + 1;
  x := x - 1;
  assert x >= 0;
}

