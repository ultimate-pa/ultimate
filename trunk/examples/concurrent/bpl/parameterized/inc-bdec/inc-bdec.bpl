//#Safe

var x : int;

procedure ULTIMATE.start()
modifies x;
free requires x == 0;
free ensures x == 0;
{
  x := x + 1;
  atomic {
    assume x > 0;
    x := x - 1;
  }
}
