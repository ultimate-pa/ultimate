type rational = { n, d: int };

type Field x;

var a: [Field rational]rational;
var b: [rational](Field rational);

procedure test (f: Field rational) returns (r:rational)
   modifies a,b;
{
   var tmp: rational;

   tmp := a[f];
   a[b[tmp]] := tmp;
   b[tmp] := f;
   r   := a[b[tmp]];
}
