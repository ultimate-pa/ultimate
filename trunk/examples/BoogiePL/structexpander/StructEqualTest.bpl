type rational = { n, d: int, v:real };

procedure test (a: rational) returns (r:rational)
{
   var tmp: rational;

   tmp := a;
   tmp!n := a!d;
   assert (tmp == a);
   call tmp := test(tmp);
   r   := tmp;
}
