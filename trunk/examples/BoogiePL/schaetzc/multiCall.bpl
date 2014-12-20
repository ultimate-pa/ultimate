procedure f()
{
   var v1, v2 : int;
   call v1 := g(v2);
   call v2 := g(v1);
}

procedure g(x : int) returns (y : int)
requires x > 1;
ensures y > 2;
{
   var l : int;
   l := 2 * x;
   y := l;
}

