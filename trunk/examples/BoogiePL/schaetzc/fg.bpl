var z, w : int;

procedure f()
modifies z,w;
{
   w := 0;
   havoc z;
   while (z < 7) {
      call z := g(z);
   }
}

procedure g(inx : int) returns (y : int)
modifies z,w;
{
   var x : int;
   x := inx;
   
   w := w + 1;
   y := x;
   x := 1;
   y := x + y;
}

