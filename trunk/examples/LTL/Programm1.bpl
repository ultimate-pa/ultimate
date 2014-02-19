/*



*/

var  x: int;

procedure ULTIMATE.start() returns ()
modifies x;
{
  x:= 10;
  while (x > 0)
  {
    x := x - 1;
  }
}