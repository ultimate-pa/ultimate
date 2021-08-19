//#Unsafe
//@ ltl invariant positive: <>(AP(x || y))

var x : bool;
var y : bool;

procedure ULTIMATE.start() returns ()
modifies x, y;
{
  havoc y;
  if (y) {
    return;
  }
  
  call P1();
}

procedure P1()
modifies x, y;
{
  if (*) {
    y := true;
  }
  if (!x) {
    x := true;
  }
}