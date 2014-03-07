// example with arrays

var a : [int] int;
var y : int;

implementation main() returns ()
{
  a[0] := 5;
  y := y + 1;
  assert a[0] == 5;
}

procedure main() returns ();
  modifies a, y;

