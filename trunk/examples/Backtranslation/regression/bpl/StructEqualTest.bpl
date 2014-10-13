type rational = { n, d: int, v:real };

procedure test (a: rational) returns (r:rational)
requires a!n == 1 && a!d == 0 && a!v == 0.0;
{
   var tmp: rational;

   tmp := a;
   tmp!n := a!d;
   assert (tmp == a);
   call tmp := test(tmp);
   r := tmp;
}
