//#Safe

var x : int;

procedure ULTIMATE.start()
modifies x;
free requires x == 0;
free ensures x == 0;
{
  var k : int;

  havoc k;
  x := x + k;
  x := x - k;
}
