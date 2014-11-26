var z, w : int;

procedure f()
{
   w := 0;
   havoc z;
   while (z < 7) {
      z := g(z);
   }
}

procedure g(x : int) returns (y : int)
{
   w := w + 1;
   y := x;
   x := 1;
   y := x + y;
}

