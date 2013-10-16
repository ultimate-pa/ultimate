type rational = { n, d: int };

function { : inline } add ( f1 : rational, f2 : rational) returns (result:rational)
   { { n: f1!n*f2!d + f1!d*f2!n, d: f1!d * f2!d }}

procedure test (a: rational) returns (r:rational)
{
   var tmp: rational;

   tmp := a;
   tmp!n := a!d;
   tmp := add(a, tmp);
   call tmp := test(tmp);
   r   := tmp;
}
