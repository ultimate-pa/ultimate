type rational = { n, d: int, v:real };

var g: rational;

procedure test (a: rational) returns (r:rational)
   modifies g;
{
   g!n := a!d;
   assert (g!d == old(g)!d);
   assert (old(g)!n == old(g!n));
   assume (g == old(g));
   r!n := old(g)!n;
   r!d := g!d;
}
