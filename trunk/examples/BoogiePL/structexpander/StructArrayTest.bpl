type rational = { n, d: int };

procedure test (a: rational) returns (r:rational)
{
   var foo : [rational]rational;
   var r2i : [rational]int;
   var i2r : [int]rational;

   foo[a] := a;
   r := foo[a];
   foo[foo[a]] := a;

   r2i := r2i[r := a!d];
   i2r := i2r[r!d := a];

   i2r[r2i[a]] := a;
   r2i[i2r[a!n]] := a!d;
   r!d := r2i[i2r[a!n]];
   r := i2r[r2i[a]];
   r := foo[foo[a]];
}
