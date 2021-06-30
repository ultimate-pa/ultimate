//#Safe
var x : int;

procedure ULTIMATE.start()
modifies x;
{
  x := 0;

  fork 1 Thread();
  fork 2,2 Thread();
  fork 3,3,3 Thread();
  join 1;
  join 2,2;
  join 3,3,3;

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
