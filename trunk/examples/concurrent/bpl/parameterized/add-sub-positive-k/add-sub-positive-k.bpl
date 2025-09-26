//#Safe

var x : int;

procedure ULTIMATE.start()
modifies x;
free requires x == 0;
free ensures x == 0;
{
  var k : int;

  havoc k;
  assume k >= 0;
  x := x + k;
  x := x - k;
}
