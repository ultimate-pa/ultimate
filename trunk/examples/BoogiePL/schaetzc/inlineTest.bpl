var g : int;
var g1, g2 : int;

procedure f()
modifies g2;
{
   call g2 := g(2 * g);
}

procedure g(x : int) returns (y : int)
requires x > 1;
ensures y > 2;
{
   var l : int;
   l := 2 * x;
   y := l;
}

