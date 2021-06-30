//#Safe
var x : int;

procedure ULTIMATE.start()
modifies x;
{
  x := 0;

  fork 1 Thread();
  join 1;

  assert x == 0;
}

procedure Thread()
modifies x;
{
  var i : int;
  while (*) {
    havoc i;
    x := x + i;
    x := x - i;
  }
}
